{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -Werror -i..  #-}

module Source.Parse(parseString) where

import Control.Monad

import Text.Parsec.Char
import Text.ParserCombinators.Parsec

import Source.Ast

parseString :: String -> String -> Either String Term
parseString fileName text = case parse pTerm fileName text of
  Left pError -> Left $ show pError
  Right term -> Right term

pTerm :: Parser Term
pTerm = try pSym <|> try pIntLit <|> try pBoolLit <|> try pAbs <|>
        try pApp <|> try pIfThenElse <|> try pBinOp <|> try pLet
  where pSym = liftM SymT variable
        pIntLit = liftM (IntT . read) $ many1 digit
        pBoolLit = liftM BoolT $ choice [try (string "true") >> return True,
                                         try (string "false") >> return False]
        pAbs = inParens $ do
          _ <- string "lam"
          spaces
          args <- inParens $  sepBy1 variable spaces
          spaces
          body <- pTerm
          return $ AbsT args body
        pApp = inParens $ do
          (left, right) <- parseDouble
          return $ AppT left right
        pIfThenElse = inParens $ do
          _ <- string "if"
          spaces
          condition <- pTerm
          spaces
          true <- pTerm
          spaces
          false <- pTerm
          return $ IfT condition true false
        pBinOp = inParens $ do
          opType <- choice operatorParsers
          spaces
          (left, right) <- parseDouble
          return $ BinT opType left right
        pLet = inParens $ do
          _ <- string "let"
          spaces
          bindings <- inParens $ sepBy1 pLetBinding spaces
          spaces
          body <- pTerm
          return $ LetT bindings body
        pLetBinding = inParens $ do
          var <- variable
          spaces
          boundTo <- pTerm
          return $ (var, boundTo)

        parseDouble = do
          left <- pTerm
          spaces
          right <- pTerm
          return (left, right)
        variable = do
          name <- many1 letter
          if name `elem` keywords then fail "keyword used as variable name"
            else return name
        inParens = between (string "(") (string ")")
        keywords = ["lam", "if", "true", "false"]
        operatorTable = [("+", PlusOp), ("-", MinusOp), ("*", MultOp),
                         ("/", DivOp), ("<", LtOp), ("==", EqOp)]
        operatorParsers = map genericOperatorParser operatorTable
        genericOperatorParser (rep, name) = string rep >> return name
