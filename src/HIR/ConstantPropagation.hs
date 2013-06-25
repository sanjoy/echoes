{-# OPTIONS_GHC -Wall -Werror -i..  #-}
{-# LANGUAGE GADTs, RankNTypes #-}

module HIR.ConstantPropagation(constantPropagationPass,
                               runConstantPropagation) where

import Compiler.Hoopl
import qualified Control.Monad as Mon
import qualified Data.Map as M

import HIR.HIR
import Source.Ast

data Constant = IntegerC Int | BooleanC Bool | ClosureC VarId
              deriving(Show, Eq, Ord)
type ConstantFact = M.Map VarId (WithTop Constant)

constantLattice :: DataflowLattice ConstantFact
constantLattice = DataflowLattice {
  fact_name = "Constant Variables",
  fact_bot = M.empty,
  fact_join = joinMaps (extendJoinDomain constantFactJoin)
  } where
  constantFactJoin _ (OldFact old) (NewFact new)
    | new == old = (NoChange, PElem new)
    | otherwise = (SomeChange, Top)

transferConstants :: FwdTransfer HNode ConstantFact
transferConstants = mkFTransfer3 closeOpen openOpen openClose
  where
    closeOpen :: HNode C O -> ConstantFact -> ConstantFact
    closeOpen LabelHN{} = id

    openOpen :: HNode O O -> ConstantFact -> ConstantFact
    openOpen (LoadArgHN _ var) = hasTop var
    openOpen (LoadIntLitHN value var) = hasConst var $ IntegerC value
    openOpen (LoadBoolLitHN value var) = hasConst var $ BooleanC value
    openOpen (LoadClosureHN value var) = hasConst var $ ClosureC value
    openOpen (BinOpHN _ _ _ var) = hasTop var
    openOpen (PushHN _ _ var) = hasTop var
    openOpen (ForceHN _ var) = hasTop var
    openOpen (Phi2HN _ _ var) = hasTop var

    hasTop var = M.insert var Top
    hasConst var value = M.insert var $ PElem value

    openClose :: HNode O C -> ConstantFact -> FactBase ConstantFact
    openClose (IfThenElseHN var tLbl fLbl) f =
      mkFactBase constantLattice $ map (
        \(lbl, value) -> (lbl, M.insert var (PElem $ BooleanC value) f))
      [(tLbl, True), (fLbl, False)]
    openClose (JumpHN lbl) f = mapSingleton lbl f
    openClose (ReturnHN _) _ = mapEmpty

loadConstant :: Constant -> VarId -> HNode O O
loadConstant (IntegerC intLit) resultVar = LoadIntLitHN intLit resultVar
loadConstant (BooleanC boolLit) resultVar = LoadBoolLitHN boolLit resultVar
loadConstant (ClosureC closureLit) resultVar =
  LoadClosureHN closureLit resultVar

newtype MaybeWithTop a = MWT (Maybe (WithTop a)) deriving(Show)
instance Monad MaybeWithTop where
  return = MWT . Just . PElem
  MWT (Just (PElem v)) >>= f =
    case f v of
      wholeExp@(MWT (Just (PElem _))) -> wholeExp
      anythingElse -> anythingElse
  MWT Nothing >>= _ = MWT Nothing
  MWT (Just Top) >>= _ = MWT $ Just Top

mwtToMby :: MaybeWithTop a -> Maybe a
mwtToMby (MWT (Just (PElem v))) = Just v
mwtToMby _ = Nothing

evaluateNode :: (VarId -> MaybeWithTop Constant) -> HNode e x -> Maybe (HNode e x)
evaluateNode f (BinOpHN op left right result) = mwtToMby $ do
  leftLit <- f left
  rightLit <- f right
  constValue <- functionFor op leftLit rightLit
  return $ loadConstant constValue result
  where functionFor :: BinOp -> Constant -> Constant -> MaybeWithTop Constant
        functionFor PlusOp = massageInt $ liftNativeI (+)
        functionFor MinusOp = massageInt $ liftNativeI (-)
        functionFor MultOp = massageInt $ liftNativeI (*)
        functionFor DivOp = \x y -> if y == IntegerC 0 then MWT Nothing
                                    else massageInt (liftNativeI div) x y
        functionFor LtOp = massageInt $ liftNativeB (<)
        functionFor EqOp = massageInt $ liftNativeB (==)

        massageInt :: (Int -> Int -> a) -> Constant -> Constant ->
                      MaybeWithTop a
        massageInt baseFn (IntegerC x) (IntegerC y) =
          MWT $ Just $ PElem $ baseFn x y
        massageInt _ _ _ = MWT Nothing

        liftNativeI native x y = IntegerC $ native x y
        liftNativeB native x y = BooleanC $ native x y
evaluateNode f (Phi2HN (varA, _) (varB, _) result) = mwtToMby $ do
  constA <- f varA
  constB <- f varB
  if constA == constB then return $ loadConstant constA result
    else MWT Nothing
evaluateNode f (IfThenElseHN condition tLbl fLbl) = mwtToMby $ do
  constC <- f condition
  case constC of
    BooleanC constCBool -> return . JumpHN $ if constCBool then tLbl else fLbl
    _ -> MWT Nothing -- TODO: we know this program has an error.
                     -- Report it somehow.
evaluateNode f (ForceHN val result) = mwtToMby $ do
  constVal <- f val
  return $ loadConstant constVal result
evaluateNode _ _ = Nothing

foldConstants :: forall m. FuelMonad m => FwdRewrite m HNode ConstantFact
foldConstants = mkFRewrite3 closeOpen openOpen openClose
  where
    closeOpen _ _ = return Nothing -- Nothing we can do for labels.

    openOpen node facts =
      return $ Mon.liftM mkMiddle $ evaluateNode (MWT . flip M.lookup facts) node

    openClose node facts =
      return $ Mon.liftM mkLast $ evaluateNode (MWT . flip M.lookup facts) node

constantPropagationPass :: FuelMonad m => FwdPass m HNode ConstantFact
constantPropagationPass = FwdPass {
  fp_lattice = constantLattice,
  fp_transfer = transferConstants,
  fp_rewrite = foldConstants
  }

runConstantPropagation :: HFunction -> M HFunction
runConstantPropagation hFunc = do
  (body, _, _) <- analyzeAndRewriteFwd constantPropagationPass
                  (JustC [hFnEntry hFunc]) (hFnBody hFunc) $
                  mapSingleton (hFnEntry hFunc) M.empty
  return hFunc{hFnBody = body}
