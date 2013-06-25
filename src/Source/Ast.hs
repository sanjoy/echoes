module Source.Ast(BinOp(..), Term(..), Id) where

data BinOp = PlusOp | MinusOp | MultOp | DivOp | LtOp | EqOp deriving(Ord, Eq)
instance Show BinOp where
  show PlusOp = "+"
  show MinusOp = "-"
  show MultOp = "*"
  show DivOp = "/"
  show LtOp = "<"
  show EqOp = "="

type Id = String
data Term = SymT Id | IntT Int | BoolT Bool | AbsT [Id] Term
          | AppT Term Term | IfT Term Term Term | BinT BinOp Term Term
          deriving(Ord, Eq)

maybeAddParens False string = string
maybeAddParens True string = "(" ++ string ++ ")"

termToString :: Bool -> Term -> String
termToString _ (SymT var) = var
termToString _ (IntT i) = show i
termToString _ (BoolT b) = show b
termToString parens (AbsT arg body) =
  maybeAddParens parens ("λ " ++ unwords arg ++ "· " ++
                         termToString False body)
termToString parens (AppT left right) =
  maybeAddParens parens (termToString True left ++ " " ++
                         termToString True right)
termToString parens (IfT c t f) =
  maybeAddParens parens ("If " ++ termToString True c ++ " then " ++
                         termToString True t ++ " else " ++
                         termToString True f)
termToString parens (BinT op left right) =
  maybeAddParens parens (termToString True left ++ " " ++ show op ++
                         " " ++ termToString True right)

instance Show Term where show = termToString False
