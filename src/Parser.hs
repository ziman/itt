module Parser (readProgram) where

import Text.Parsec

import TT
import Inference (Evar(..))

type ParserState = Int  -- for fresh evars
type Term = TT Evar
type Parser a = Parsec String ParserState a

readProgram :: String -> IO (Either ParseError Term)
readProgram fname = do
    code <- readFile fname
    return $ runParser term 1 fname code

term :: Parser Term
term = undefined
