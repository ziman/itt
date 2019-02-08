module Inference where

import TT
import Prelude hiding (lookup, foldr)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.RWS.Strict

data Evar = EV Int | Q Q deriving (Eq, Ord)

instance Show Evar where
    show (EV i) = show i
    show (Q q) = show q

type Env r = M.Map Name (r, TT r)

data ConstrRHS = CEV Evar | (:~) (TT Evar) (TT Evar) deriving (Eq, Ord)

instance Show ConstrRHS where
    show (CEV v) = show v
    show (p :~ q) = show p ++ " ~ " ++ show q

data Constr = (:->) (S.Set Evar) ConstrRHS deriving (Eq, Ord)

instance Show Constr where
    show (gs :-> rhs) = show (S.toList gs) ++ " -> " ++ show rhs

type Constrs = S.Set Constr

type Term = TT Evar
type Type = TT Evar

data TCEnv = TCEnv
    { tcEnv :: Env Evar
    , tcGuards :: S.Set Evar
    , tcBacktrace :: [String]
    }

data TCErrMsg
    = CantCheck Term
    | UnknownVar Name
    | NotPi Type
    deriving (Eq, Ord, Show)

data TCFailure = TCFailure
    { tcfMessage :: TCErrMsg
    , tcfBacktrace :: [String]
    }
    deriving (Eq, Ord, Show)

newtype TCState = TCState { freshI :: Int }

type TC a = RWST
    TCEnv           -- R: environment + guards
    Constrs         -- W: constraints
    TCState         -- S: for fresh names
    (Except TCFailure) -- T: errors
    a

tcfail :: TCErrMsg -> TC a
tcfail err = do
    bt <- tcBacktrace <$> ask
    lift . throwE $ TCFailure err bt

bt :: Show a => a -> TC b -> TC b
bt item = local $
    \(TCEnv env gs bt)
        -> TCEnv env gs (show item : bt)

given :: Evar -> TC b -> TC b
given g = local $
    \(TCEnv env gs bt)
        -> TCEnv env (S.insert g gs) bt

lookup :: Name -> TC (Evar, Type)
lookup n = do
    env <- tcEnv <$> ask
    case M.lookup n env of
        Nothing -> tcfail $ UnknownVar n
        Just rty -> return rty

assert :: ConstrRHS -> TC ()
assert cr = do
    gs <- tcGuards <$> ask
    tell [gs :-> cr]

(~=) :: Term -> Term -> TC ()
l ~= r = assert (rnf l :~ rnf r)

(<->) :: Evar -> Evar -> TC ()
p <-> q = tell [[p] :-> CEV q, [q] :-> CEV p]

with :: (Name, Evar, Type) -> TC b -> TC b
with (n, r, ty) = local $
    \(TCEnv env gs bt)
        -> TCEnv (M.insert n (r, ty) env) gs bt

inferTm :: Term -> TC Type
inferTm (V n) = do
    (r, ty) <- lookup n
    assert (CEV r)
    return ty    

inferTm (Lam n r ty rhs) = do
    tyty <- given (Q E) $ inferTm ty
    tyty ~= Type
    rty <- with (n, r, ty) $ inferTm rhs
    return $ Pi n r ty rty

inferTm (Pi n r ty rhs) = do
    tyty <- given (Q E) $ inferTm ty
    tyty ~= Type

    rty <- with (n, r, ty) $ given (Q E) $ inferTm rhs
    rty ~= Type

    return Type

inferTm (App r f x) = do
    fty <- inferTm f
    xty <- given r $ inferTm x

    case rnf fty of
        Pi n' r' ty' rhs' -> do
            xty ~= ty'
            r <-> r'
            return $ subst n' x rhs'
            
        fty' -> tcfail $ NotPi fty'

inferTm Type = pure Type

infer :: Term -> Either TCFailure (Type, Constrs)
infer tm = runExcept $ evalRWST (inferTm tm) (TCEnv M.empty [] []) TCState{freshI = 0}
