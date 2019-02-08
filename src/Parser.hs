module Parser (readProgram) where

import Prelude hiding (pi)
import Data.Char
import Text.Parsec
import Control.Monad

import TT
import Inference (Evar(..))

type ParserState = Int  -- for fresh evars
type Term = TT Evar
type Parser a = Parsec String ParserState a

readProgram :: String -> IO (Either ParseError Term)
readProgram fname = do
    code <- readFile fname
    return $ runParser (sp *> term) 1 fname code

comment :: Parser ()
comment = do
    kwd "--"
    many $ satisfy (/= '\n')
    sp

spaces1 :: Parser ()
spaces1 = many1 (satisfy isSpace) *> pure ()

sp :: Parser ()
sp = many (spaces1 <|> comment) *> pure ()

kwd :: String -> Parser ()
kwd s = try (string s) >> sp

parens :: Parser a -> Parser a
parens p = kwd "(" *> p <* kwd ")"

nrty :: Parser (Name, Evar, Term)
nrty = (,,) <$> name <*> evar <*> term

freshEvar :: Parser Evar
freshEvar = do
    i <- getState
    putState (i+1)
    return $ EV i

name :: Parser Name
name = do
    n <- many1 $ satisfy (\c -> isAlpha c || isDigit c || c `elem` "'-_")
    sp
    return $ N n 0

evar :: Parser Evar
evar =
    (kwd ":I" *> pure (Q I))
    <|> (kwd ":E" *> pure (Q E))
    <|> (kwd ":R" *> pure (Q R))
    <|> (kwd ":" *> freshEvar)

lam :: Parser Term
lam = do
    kwd "\\"
    (n, r, ty) <- nrty
    kwd "."
    rhs <- term
    return $ Lam n r ty rhs

pi :: Parser Term
pi = do
    (n, r, ty) <- parens nrty
    kwd "->"
    rhs <- term
    return $ Pi n r ty rhs

atom :: Parser Term
atom = parens term <|> (V <$> name)

app :: Parser Term
app = do
    f:xs <- many1 atom
    foldM (\f x -> App <$> freshEvar <*> pure f <*> pure x) f xs

term :: Parser Term
term = (kwd "Type" *> pure Type) <|> lam <|> pi <|> app
