module Inference where

import Prelude hiding (lookup, foldr)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.RWS.Strict
import qualified Data.Map as M
import qualified Data.Set as S

import TT
import Pretty

data Evar = EV Int | Q Q deriving (Eq, Ord)

instance PrettyR Evar where
    prettyApp (EV i) = text "-" <> int i <> text "-"
    prettyApp (Q q)  = text "-" <> pretty q <> text "-"

    prettyCol (EV i) = text ":" <> int i
    prettyCol (Q q)  = text ":" <> pretty q

instance Show Evar where
    show (EV i) = show i
    show (Q q) = show q

type Env r = M.Map Name (r, TT r)

newtype Backtrace = BT { btLines :: [String] }

instance Eq Backtrace where
    _ == _ = True

instance Ord Backtrace where
    compare _ _ = EQ

instance Show Backtrace where
    show _ = "_bt"

infixr 3 :->
data (:->) a b = (:->) a b deriving (Eq, Ord)

class ShowRHS a where
    showRHS :: a -> String

instance ShowRHS (Backtrace, TT Evar, TT Evar) where
    showRHS (_bt, lhs, rhs) = show lhs ++ " ~ " ++ show rhs

instance ShowRHS Evar where
    showRHS = show

instance ShowRHS b => Show (S.Set Evar :-> b) where
    show (gs :-> y) = show (S.toList gs) ++ " -> " ++ showRHS y

data Constrs = Constrs
    { csConvs :: S.Set (S.Set Evar :-> (Backtrace, TT Evar, TT Evar))
    , csImpls :: [S.Set Evar :-> Evar]
    , csEqs   :: S.Set (Evar, Evar)
    }

instance Semigroup Constrs where
    Constrs cs is es <> Constrs cs' is' es'
        = Constrs (cs <> cs') (is <> is') (es <> es')

instance Monoid Constrs where
    mempty = Constrs [] [] []

type Term = TT Evar
type Type = TT Evar

data TCEnv = TCEnv
    { tcEnv :: Env Evar
    , tcGuards :: S.Set Evar
    , tcBacktrace :: Backtrace
    }

data TCErrMsg
    = CantCheck Term
    | UnknownVar Name
    | NotPi Type
    deriving (Eq, Ord, Show)

data TCFailure = TCFailure
    { tcfMessage :: TCErrMsg
    , tcfBacktrace :: Backtrace
    }
    deriving (Eq, Ord)

instance Show TCFailure where
    show TCFailure{tcfMessage, tcfBacktrace = BT bt} =
        "With backtrace:\n" ++ unlines (map ("  "++) $ reverse bt)
        ++ "!! " ++ show tcfMessage

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
    \(TCEnv env gs (BT bt))
        -> TCEnv env gs $ BT (show item : bt)

given :: Evar -> TC b -> TC b
given g = local $
    \(TCEnv env gs bt)
        -> TCEnv env (S.insert g gs) bt

irr :: TC b -> TC b
irr = local $
    \(TCEnv env gs bt)
        -> TCEnv (irrEnv env) (S.singleton $ Q I) bt

irrEnv :: Env Evar -> Env Evar
irrEnv = M.map $ \(q, ty) -> (Q I, ty)

lookup :: Name -> TC (Evar, Type)
lookup n = do
    env <- tcEnv <$> ask
    case M.lookup n env of
        Nothing -> tcfail $ UnknownVar n
        Just rty -> return rty

(~=) :: Term -> Term -> TC ()
l ~= r = do
    gs <- tcGuards    <$> ask
    bt <- tcBacktrace <$> ask
    tell mempty{ csConvs = [gs :-> (bt, l, r)] }

budget :: Evar -> TC ()
budget r = do
    gs <- tcGuards <$> ask
    tell mempty{ csImpls = [gs :-> r] }

(<->) :: Evar -> Evar -> TC ()
p <-> q = do
    bt <- tcBacktrace <$> ask
    tell mempty{ csEqs = [(min p q, max p q)] }

with :: (Name, Evar, Type) -> TC b -> TC b
with (n, r, ty) = local $
    \(TCEnv env gs bt)
        -> TCEnv (M.insert n (r, ty) env) gs bt

inferTm :: Term -> TC Type
inferTm (V n) = bt ("VAR", n) $ do
    (r, ty) <- lookup n
    budget r
    return ty    

inferTm (Lam n r ty rhs) = bt ("LAM", n) $ do
    tyty <- irr $ inferTm ty
    tyty ~= Type
    tell mempty{ csImpls = [[Q I] :-> r] }  -- make the binder mentioned in the constraints
    rty <- with (n, r, ty) $ inferTm rhs
    return $ Pi n r ty rty

inferTm (Pi n r ty rhs) = bt ("PI", n) $ do
    tyty <- irr $ inferTm ty
    tyty ~= Type

    rty <- with (n, r, ty) $ irr $ inferTm rhs
    rty ~= Type

    return Type

inferTm (App r f x) = bt ("APP", f) $ do
    fty <- bt "LHS" $ inferTm f
    xty <- bt ("RHS", fty) $ given r $ inferTm x

    case rnf fty of
        Pi n' r' ty' rhs' -> do
            xty ~= ty'
            r <-> r'
            return $ subst n' x rhs'
            
        fty' -> tcfail $ NotPi fty'

inferTm Type = pure Type

infer :: Term -> Either TCFailure (Type, Constrs)
infer tm = runExcept $ evalRWST (inferTm tm) (TCEnv M.empty [] $ BT []) TCState{freshI = 0}
