{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving #-}

module HIR.HIR(termToHIR, HNode(..), HFunction(..),
               VarId, InpId, ResId, getVarsRead, getVarsWritten,
               hirDebugShowGraph)
       where

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
type FunctionId = Int
type ArgId = Int
data LiftedFunction = LiftedFunction FunctionId Int LiftedTerm deriving(Show, Ord, Eq)
data LiftedTerm = ArgLT ArgId | IntLT Int | BoolLT Bool | FuncLT FunctionId
                | AppLT LiftedTerm LiftedTerm | IfLT LiftedTerm LiftedTerm LiftedTerm
                | BinLT BinOp LiftedTerm LiftedTerm deriving(Show, Ord, Eq)

data LoweringState = LoweringState [LiftedFunction] [FunctionId]
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

    createFunction :: Int -> LiftedTerm -> LiftM FunctionId
    createFunction argC body = do
      (LoweringState fnList (newName:names)) <- St.get
      St.put $ LoweringState (LiftedFunction newName argC body:fnList) names
      return newName

{-  HNode defines an SSA IR to which we transform each function for
 -  mization.It uses the Hoopl library.  The 'H' stands for 'high-level' -}

type VarId = Int
type InpId = VarId
type ResId = VarId

data HNode e x where
  LabelHN :: Label -> HNode C O

  LoadArgHN :: InpId -> ResId -> HNode O O
  LoadIntLitHN :: Int -> ResId -> HNode O O
  LoadBoolLitHN :: Bool -> ResId -> HNode O O
  LoadClosureHN :: InpId -> ResId -> HNode O O
  -- Operator -> LeftOp -> RightOp -> Result
  BinOpHN :: BinOp -> InpId -> InpId -> ResId -> HNode O O
  -- Function -> Arg -> Result
  PushHN :: InpId -> InpId -> ResId -> HNode O O
  ForceHN :: InpId -> ResId -> HNode O O
  Phi2HN :: (InpId, Label) -> (InpId, Label) -> ResId -> HNode O O

  IfThenElseHN :: InpId -> Label -> Label -> HNode O C
  JumpHN :: Label -> HNode O C
  ReturnHN :: InpId -> HNode O C
deriving instance Show(HNode e x)

instance NonLocal HNode where
  entryLabel (LabelHN label) = label
  successors (IfThenElseHN _ tLabel fLabel) = [tLabel, fLabel]
  successors (JumpHN label) = [label]
  successors (ReturnHN _) = []

getVarsRead :: forall e x. HNode e x -> [VarId]
getVarsRead = fst . getVRW

getVarsWritten :: forall e x. HNode e x -> [VarId]
getVarsWritten = snd . getVRW

getVRW :: forall e x. HNode e x -> ([VarId], [VarId])
getVRW LabelHN{} = ([], [])
getVRW (LoadArgHN inp out) = ([inp], [out])
getVRW (LoadBoolLitHN _ out) = ([], [out])
getVRW (LoadIntLitHN _ out) = ([], [out])
getVRW (LoadClosureHN _ out) = ([], [out])
getVRW (BinOpHN _ inA inB out) = ([inA, inB], [out])
getVRW (PushHN inA inB out) = ([inA, inB], [out])
getVRW (ForceHN inp out) = ([inp], [out])
getVRW (Phi2HN (inA, _) (inB, _) out) = ([inA, inB], [out])
getVRW (IfThenElseHN inp _ _) = ([inp], [])
getVRW JumpHN{} = ([], [])
getVRW (ReturnHN inp) = ([inp], [])

data HFunction = HFunction { hFnName :: FunctionId, hFnArgCount :: Int,
                             hFnEntry :: Label, hFnBody :: Graph HNode C C }

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
  ((fullTermTranslated, entry), _) <-
    St.runStateT (liftedTermToHIR fullTerm) [0..]
  return HFunction{hFnName = fnId, hFnArgCount = argC, hFnEntry = entry,
                   hFnBody = fullTermTranslated}

liftedTermToHIR :: LiftedTerm -> HIRMonad (Graph HNode C C, Label)
liftedTermToHIR fullTerm = do
  entry <- freshLabel
  (functionBody, resultVar) <- emit fullTerm
  let fullGraph = mkFirst (LabelHN entry) <*> functionBody <*>
                  mkLast (ReturnHN resultVar)
  return (fullGraph, entry)
  where emit :: LiftedTerm -> HIRMonad (Graph HNode O O, VarId)
        emit (ArgLT argId) = loadSimple (LoadArgHN argId)
        emit (IntLT intLit) = loadSimple (LoadIntLitHN intLit)
        emit (BoolLT boolLit) = loadSimple (LoadBoolLitHN boolLit)
        emit (FuncLT functionId) = loadSimple (LoadClosureHN functionId)
        emit (AppLT function arg) = do
          (functionCode, functionVar) <- emit function
          (argCode, argVar) <- emit arg
          forcedFnVar <- freshVarName
          resultVar <- freshVarName
          let finalBody = functionCode <*>
                          argCode <*>
                          mkMiddle (ForceHN functionVar forcedFnVar) <*>
                          mkMiddle (PushHN forcedFnVar argVar resultVar)
          return (finalBody, resultVar)
        emit (IfLT condition trueBranch falseBranch) = do
          (conditionCode, condVar) <- emit condition
          finalLabel <- freshLabel
          forcedCondVar <- freshVarName
          resultVar <- freshVarName
          (tCode, tLabel, tRes) <- emitIfBranch trueBranch finalLabel
          (fCode, fLabel, fRes) <- emitIfBranch falseBranch finalLabel
          let ifThenElse =
                conditionCode <*> mkMiddle (ForceHN condVar forcedCondVar) <*>
                mkLast (IfThenElseHN forcedCondVar tLabel fLabel) |*><*|
                tCode |*><*| fCode |*><*| mkFirst (LabelHN finalLabel) <*>
                mkMiddle (Phi2HN (tRes, tLabel) (fRes, fLabel) resultVar)
          return (ifThenElse, resultVar)
        emit (BinLT op left right) = do
          (leftG, leftVar) <- emit left
          (rightG, rightVar) <- emit right
          forcedLeftVar <- freshVarName
          forcedRightVar <- freshVarName
          resultVar <- freshVarName
          let computeBinOp =
                leftG <*> rightG <*> mkMiddles [
                  ForceHN leftVar forcedLeftVar,
                  ForceHN rightVar forcedRightVar,
                  BinOpHN op forcedLeftVar forcedRightVar resultVar]
          return (computeBinOp, resultVar)

        loadSimple loader = do varName <- freshVarName
                               return (mkMiddle $ loader varName, varName)
        emitIfBranch term finalLabel = do
          branchLabel <- freshLabel
          (termBody, termResult) <- emit term
          let termCode = mkFirst (LabelHN branchLabel) <*> termBody <*>
                         mkLast (JumpHN finalLabel)
          return (termCode, branchLabel, termResult)
        freshVarName = St.StateT (\(name:names) -> return (name, names))


type HIRMonad a = St.StateT [VarId] M a
instance UniqueMonad m => UniqueMonad (St.StateT s m) where
  freshUnique = St.StateT (\s -> St.liftM (\u -> (u, s)) freshUnique)



{-  Debugging tools.  -}

hirDebugShowGraph :: M [HFunction] -> String
hirDebugShowGraph fn =
  let functionList = runSimpleUniqueMonad $ runWithFuel fuel fn
  in L.intercalate "\n\n" $ map showHFunction functionList
  where
    showHFunction (HFunction name argC entry body) =
      "FunctionId = " ++ show name ++ "\n" ++
      "ArgCount  = " ++ show argC ++ "\n" ++
      "EntryLabel = " ++ show entry ++ "\n" ++
      "Body {\n" ++ showGraph ((++ " ") . show) body ++  "}\n"
    fuel = 999999
