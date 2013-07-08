{-# OPTIONS_GHC -Wall -Werror -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving #-}

module HIR.HIR(termToHIR, HNode(..), HFunction(..), InpId, ResId, Lit(..),
               getHVarsRead, getHVarsWritten, hirDebugShowGraph) where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as Mby
import qualified Data.Set as S
import qualified Control.Monad.State as St
import Compiler.Hoopl


import Source.Ast
import Utils.Common

getOpenVariables :: S.Set Id -> Term -> S.Set Id
getOpenVariables env (SymT var) =
  if S.member var env then S.empty else S.singleton var
getOpenVariables _ (IntT _) = S.empty
getOpenVariables _ (BoolT _) = S.empty
getOpenVariables env (AbsT arg body) =
  getOpenVariables (S.fromList arg `S.union` env) body
getOpenVariables env (AppT fn arg) =
  S.unions $ map (getOpenVariables env) [fn, arg]
getOpenVariables env (IfT c t f) =
  S.unions $ map (getOpenVariables env) [c, t, f]
getOpenVariables env (BinT _ l r) =
  S.unions $ map (getOpenVariables env) [l, r]

isClosed :: Term -> Bool
isClosed = S.null . getOpenVariables S.empty

{- Make closures explicit -- symbols that would normally capture
 - values from the lexical environment are now passed in explicitly as
 - parameters.-}

openLambdas :: Term -> Term
openLambdas (SymT var) = SymT var
openLambdas (IntT lit) = IntT lit
openLambdas (BoolT lit) = BoolT lit
openLambdas wholeExp@(AbsT arg body) =
  let processedBody = openLambdas body
      subtermOpenVars = S.toList (getOpenVariables S.empty wholeExp)
  in L.foldl (\prevClosure var -> (AppT prevClosure (SymT var)))
     (AbsT (subtermOpenVars ++ arg) processedBody) subtermOpenVars
openLambdas (AppT left right) =
  AppT (openLambdas left) (openLambdas right)
openLambdas (IfT cond true false) =
  IfT (openLambdas cond) (openLambdas true) (openLambdas false)
openLambdas (BinT op left right) =
  BinT op (openLambdas left) (openLambdas right)


{- After the openLambdas phase, we "lift" the lambda bodies out of their
 - invocation point into separate Functions. -}
type ArgId = Int
data LiftedFunction = LiftedFunction ClsrId Int LiftedTerm deriving(Show, Ord, Eq)
data LiftedTerm = ArgLT ArgId | IntLT Int | BoolLT Bool | FuncLT ClsrId
                | AppLT LiftedTerm LiftedTerm | IfLT LiftedTerm LiftedTerm LiftedTerm
                | BinLT BinOp LiftedTerm LiftedTerm deriving(Show, Ord, Eq)

data LoweringState = LoweringState [LiftedFunction] [ClsrId]
type LiftM = St.State LoweringState

liftTerm :: Term -> LiftM LiftedTerm
liftTerm = liftWithEnv M.empty
  where
    liftWithEnv :: M.Map Id Int -> Term -> LiftM LiftedTerm
    liftWithEnv env (SymT var) =
      return $ ArgLT $ Mby.fromJust $ M.lookup var env
    liftWithEnv _ (IntT lit) = return $ IntLT lit
    liftWithEnv _ (BoolT lit) = return $ BoolLT lit
    liftWithEnv _ (AbsT args body) = do
      let freshEnv = M.fromList $ zip args [0..]
      newLiftedFn <- liftWithEnv freshEnv body
      newFnName <- createFunction (length args) newLiftedFn
      return $ FuncLT newFnName
    liftWithEnv env (AppT left right) = do
      liftedLeft <- liftWithEnv env left
      liftedRight <- liftWithEnv env right
      return $ AppLT liftedLeft liftedRight
    liftWithEnv env (IfT condition true false) = do
      liftedCondition <- liftWithEnv env condition
      liftedTrue <- liftWithEnv env true
      liftedFalse <- liftWithEnv env false
      return $ IfLT liftedCondition liftedTrue liftedFalse
    liftWithEnv env (BinT op left right) = do
      liftedLeft <- liftWithEnv env left
      liftedRight <- liftWithEnv env right
      return $ BinLT op liftedLeft liftedRight

    createFunction :: Int -> LiftedTerm -> LiftM ClsrId
    createFunction argC body = do
      (LoweringState fnList (newName:names)) <- St.get
      St.put $ LoweringState (LiftedFunction newName argC body:fnList) names
      return newName

{-  HNode defines an SSA IR to which we transform each function for
 -  mization.It uses the Hoopl library.  The 'H' stands for 'high-level' -}

type InpId = SSAVar
type ResId = SSAVar
data Lit = BoolL Bool | IntL Int | ClsrL ClsrId deriving(Show, Eq, Ord)

data HNode e x where
  LabelHN :: Label -> HNode C O

  LoadArgHN :: InpId -> ResId -> HNode O O
  LoadLitHN :: Lit -> ResId -> HNode O O

  -- Operator -> LeftOp -> RightOp -> Result
  BinOpHN :: BinOp -> Rator Int -> Rator Int -> ResId -> HNode O O
  -- Function -> Arg -> Result
  PushHN :: Rator ClsrId -> Rator Lit -> ResId -> HNode O O
  ForceHN :: Rator Lit -> ResId -> HNode O O
  Phi2HN :: (Rator Lit, Label) -> (Rator Lit, Label) -> ResId -> HNode O O
  -- In essence a no-op; RemoveBadPhis replaces illegal phi nodes with
  -- this.
  CopyValueHN :: Rator Lit -> ResId -> HNode O O

  IfThenElseHN :: Rator Bool -> Label -> Label -> HNode O C
  JumpHN :: Label -> HNode O C
  ReturnHN :: Rator Lit -> HNode O C
deriving instance Show(HNode e x)

instance NonLocal HNode where
  entryLabel (LabelHN label) = label
  successors (IfThenElseHN _ tLabel fLabel) = [tLabel, fLabel]
  successors (JumpHN label) = [label]
  successors (ReturnHN _) = []

getHVarsRead :: forall e x. HNode e x -> [SSAVar]
getHVarsRead = fst . getVRW

getHVarsWritten :: forall e x. HNode e x -> [SSAVar]
getHVarsWritten = snd . getVRW

getVRW :: forall e x. HNode e x -> ([SSAVar], [SSAVar])
getVRW LabelHN{} = ([], [])
getVRW (CopyValueHN inp out) = (ratorToList [inp], [out])
getVRW (LoadArgHN inp out) = ([inp], [out])
getVRW (LoadLitHN _ out) = ([], [out])
getVRW (BinOpHN _ inA inB out) = (ratorToList [inA, inB], [out])
getVRW (PushHN inA inB out) = (ratorToList [inA] ++ ratorToList [inB], [out])
getVRW (ForceHN inp out) = (ratorToList [inp], [out])
getVRW (Phi2HN (inA, _) (inB, _) out) = (ratorToList [inA, inB], [out])
getVRW (IfThenElseHN condition _ _) = (ratorToList [condition], [])
getVRW JumpHN{} = ([], [])
getVRW (ReturnHN value) = (ratorToList [value], [])

ratorToList :: [Rator a] -> [SSAVar]
ratorToList = concatMap (\r -> case r of
                            (VarR var) -> [var]
                            _ -> [])

data HFunction = HFunction { hFnName :: ClsrId, hFnArgCount :: Int,
                             hFnEntry :: Label, hFnBody :: Graph HNode C C,
                             hFnLastSSAVar :: SSAVar }

termToHIR :: Term -> Maybe (M [HFunction])
termToHIR term = if isClosed term then Just compiledTerm else Nothing
  where compiledTerm = let openedTerm = openLambdas term
                           liftedTerm = runLifting openedTerm
                       in mapM liftedFunctionToHIR liftedTerm

        runLifting openedTerm =
          let (mainTerm, LoweringState fns _) =
                St.runState (liftTerm openedTerm) (LoweringState [] [1..])
          in LiftedFunction 0 0 mainTerm:fns

liftedFunctionToHIR :: LiftedFunction -> M HFunction
liftedFunctionToHIR (LiftedFunction fnId argC fullTerm) = do
  ((fullTermTranslated, entry), lastSSAVar, _) <-
    runIRMonad (liftedTermToHIR fullTerm) 0 ()
  return HFunction{hFnName = fnId, hFnArgCount = argC, hFnEntry = entry,
                   hFnBody = fullTermTranslated, hFnLastSSAVar = lastSSAVar }

liftedTermToHIR :: LiftedTerm -> IRMonad () (Graph HNode C C, Label)
liftedTermToHIR fullTerm = do
  entry <- freshLabel
  (functionBody, resultVar) <- emit fullTerm
  let fullGraph = mkFirst (LabelHN entry) <*> functionBody <*>
                  mkLast (ReturnHN $ VarR resultVar)
  return (fullGraph, entry)
  where emit :: LiftedTerm -> IRMonad () (Graph HNode O O, SSAVar)
        emit (ArgLT argId) = loadSimple (LoadArgHN argId)
        emit (IntLT intLit) = loadSimple (LoadLitHN $ IntL intLit)
        emit (BoolLT boolLit) = loadSimple (LoadLitHN $ BoolL boolLit)
        emit (FuncLT clsrId) = loadSimple (LoadLitHN $ ClsrL clsrId)
        emit (AppLT function arg) = do
          (functionCode, functionVar) <- emit function
          (argCode, argVar) <- emit arg
          forcedFnVar <- freshVarName
          resultVar <- freshVarName
          let finalBody = functionCode <*>
                          argCode <*>
                          mkMiddle (ForceHN (VarR functionVar) forcedFnVar) <*>
                          mkMiddle (PushHN (VarR forcedFnVar) (VarR argVar)
                                    resultVar)
          return (finalBody, resultVar)
        emit (IfLT condition trueBranch falseBranch) = do
          (conditionCode, condVar) <- emit condition
          finalLabel <- freshLabel
          forcedCondVar <- freshVarName
          resultVar <- freshVarName
          (tCode, tLabel, tRes) <- emitIfBranch trueBranch finalLabel
          (fCode, fLabel, fRes) <- emitIfBranch falseBranch finalLabel
          let ifThenElse =
                conditionCode <*>
                mkMiddle (ForceHN (VarR condVar) forcedCondVar) <*>
                mkLast (IfThenElseHN (VarR forcedCondVar) tLabel fLabel) |*><*|
                tCode |*><*| fCode |*><*| mkFirst (LabelHN finalLabel) <*>
                mkMiddle (Phi2HN (VarR tRes, tLabel)
                          (VarR fRes, fLabel) resultVar)
          return (ifThenElse, resultVar)
        emit (BinLT op left right) = do
          (leftG, leftVar) <- emit left
          (rightG, rightVar) <- emit right
          forcedLeftVar <- freshVarName
          forcedRightVar <- freshVarName
          resultVar <- freshVarName
          let computeBinOp =
                leftG <*> rightG <*> mkMiddles [
                  ForceHN (VarR leftVar) forcedLeftVar,
                  ForceHN (VarR rightVar) forcedRightVar,
                  BinOpHN op (VarR forcedLeftVar) (VarR forcedRightVar)
                  resultVar]
          return (computeBinOp, resultVar)

        loadSimple loader = do varName <- freshVarName
                               return (mkMiddle $ loader varName, varName)
        emitIfBranch term finalLabel = do
          branchLabel <- freshLabel
          (termBody, termResult) <- emit term
          let termCode = mkFirst (LabelHN branchLabel) <*> termBody <*>
                         mkLast (JumpHN finalLabel)
          return (termCode, branchLabel, termResult)



{-  Debugging tools.  -}

hirDebugShowGraph :: M [HFunction] -> String
hirDebugShowGraph fn =
  let functionList = runSimpleUniqueMonad $ runWithFuel maxBound fn
  in unlines $ map showHFunction functionList
  where
    showHFunction :: HFunction -> String
    showHFunction (HFunction name argC entry body _) =
      let functionGraph = showGraph ((++ " ") . show) body
      in unlines ["ClsrId = " ++ show name, "ArgCount = " ++ show argC,
                  "EntryLabel = " ++ show entry, "Body = {",
                  functionGraph ++ "}"]
