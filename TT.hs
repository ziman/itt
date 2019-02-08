{-# LANGUAGE OverloadedLists #-}
module TT where

import Data.Foldable
import Prelude hiding (lookup, foldr)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.RWS.Strict

data Name = N String Int deriving (Eq, Ord)

instance Show Name where
    show (N s 0) = s
    show (N s i) = s ++ show i

data Q = I | E | R deriving (Eq, Ord, Show)

instance Semigroup Q where
    (<>) = min

instance Monoid Q where
    mempty  = R
    mappend = min

data TT r
    = V Name
    | Lam Name r (TT r) (TT r)
    | Pi  Name r (TT r) (TT r)
    | App r (TT r) (TT r)
    | Type
    deriving (Eq, Ord)

instance Show r => Show (TT r) where
    show (V n) = show n
    show (Lam n r ty rhs) = "(\\" ++ show n ++ " :" ++ show r ++ ": " ++ show ty ++ ". " ++ show rhs ++ ")"
    show (Pi n r ty rhs)  = "(" ++ show n ++ " :" ++ show r ++ ": " ++ show ty ++ ") -> " ++ show rhs
    show (App r f x) = show f ++ " @" ++ show r ++ " " ++ show x
    show Type = "Type"

infix 6 `freeIn`
freeIn :: Name -> TT r -> Bool
n `freeIn` V n' = n == n'
n `freeIn` Lam n' r ty rhs = n `freeIn` ty || (n /= n' && n `freeIn` rhs)
n `freeIn` Pi  n' r ty rhs = n `freeIn` ty || (n /= n' && n `freeIn` rhs)
n `freeIn` App r f x = n `freeIn` f || n `freeIn` x
n `freeIn` Type = False

subst :: Name -> TT r -> TT r -> TT r
subst n x tm@(V n')
    | n' == n   = x
    | otherwise = tm
subst n x tm@(Lam n'@(N ln li) r' ty' rhs')
    | n' == n   = tm
    | n' `freeIn` x = subst n x $ Lam n'' r' ty' (subst n' (V n'') rhs')
    | otherwise = Lam n' r' (subst n x ty') (subst n x rhs')
  where
    n'' = N ln (li + 1)

subst n x tm@(Pi n'@(N ln li) r' ty' rhs')
    | n' == n   = tm
    | n' `freeIn` x = subst n x $ Pi n'' r' ty' (subst n' (V n'') rhs')
    | otherwise = Pi n' r' (subst n x ty') (subst n x rhs')
  where
    n'' = N ln (li + 1)

subst n x (App r f y) = App r (subst n x f) (subst n x y)

subst _ _ Type = Type

rnf :: TT r -> TT r
rnf (V n) = V n
rnf (Lam n r ty rhs) = Lam n r (rnf ty) (rnf rhs)
rnf (Pi  n r ty rhs) = Pi  n r (rnf ty) (rnf rhs)
rnf (App r f x)
    | Lam n' r' ty' rhs' <- rnf f
    = rnf $ subst n' x rhs'

    | otherwise
    = App r (rnf f) (rnf x)
rnf tm@Type = tm

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

fillR :: M.Map Int Q -> Evar -> Q
fillR evars (EV i) = M.findWithDefault I i evars
fillR evars (Q  q) = q

fill :: M.Map Int Q -> TT Evar -> TT Q
fill evars (V n) = V n
fill evars (Lam n r ty rhs) = Lam n (fillR evars r) (fill evars ty) (fill evars rhs)
fill evars (Pi n r ty rhs) = Pi n (fillR evars r) (fill evars ty) (fill evars rhs)
fill evars (App r f x) = App (fillR evars r) (fill evars f) (fill evars x)
fill evars Type = Type

data ConvErr
    = CantConvert Term Term
    deriving (Eq, Ord, Show)

conv :: Term -> Term -> Except ConvErr Constrs
conv (V n) (V n') | n == n' = return S.empty
conv (Lam n r ty rhs) (Lam n' r' ty' rhs') = do
    tycs  <- conv ty ty'
    rhscs <- conv rhs $ subst n' (V n) rhs'
    return $ tycs `S.union` rhscs `S.union` [[r] :-> CEV r', [r'] :-> CEV r]

conv (Pi n r ty rhs) (Pi n' r' ty' rhs') = do
    tycs  <- conv ty ty'
    rhscs <- conv rhs $ subst n' (V n) rhs'
    return $ tycs `S.union` rhscs `S.union` [[r] :-> CEV r', [r'] :-> CEV r]

conv (App r f x) (App r' f' x') = do
    fcs <- conv f f'
    return $ fcs `S.union` [[r] :-> CEV r', [r'] :-> CEV r, [r] :-> (x :~ x')]

conv Type Type = return S.empty

conv p q = throwE $ CantConvert p q


infer :: Term -> Either TCFailure (Type, Constrs)
infer tm = runExcept $ evalRWST (inferTm tm) (TCEnv M.empty [] []) TCState{freshI = 0}

solve :: Constrs -> M.Map Int Q -> M.Map Int Q
solve cs evars
    | evars' == evars = evars
    | otherwise = solve cs evars'
  where
    evars' = foldr addConstr evars cs

    addConstr c@(gs :-> CEV (Q q))
        | vals evars gs <= q = id
        | otherwise    = error $ "inconsistent constraint: " ++ show c
    addConstr (gs :-> CEV (EV i)) = M.insert i (vals evars gs)
    addConstr (gs :-> (_ :~ _)) = id

val :: M.Map Int Q -> Evar -> Q
val evars (EV i) = M.findWithDefault I i evars
val _ (Q q)  = q

vals :: Foldable t => M.Map Int Q -> t Evar -> Q
vals evars = fold . map (val evars) . toList

check :: Term -> IO ()
check tm = case infer tm of
    Left err -> print err
    Right (ty, cs) -> do
        putStrLn "### Constraints ###\n"
        print tm
        putStrLn $ "  : " ++ show ty
        putStrLn ""
        putStrLn $ unlines ["  " ++ show c | c <- S.toList cs]

        putStrLn "### Solution ###\n"
        let iter i cs ee@(evars, eqs) = do
                putStrLn $ "-> iteration " ++ show i
                let evars' = solve cs evars
                    eqs' = S.fromList [(p, q) | (gs :-> (p :~ q)) <- S.toList cs, vals evars' gs > I]
                    ee' = (evars', eqs')
                if ee == ee'
                    then return evars
                    else do
                        putStrLn "  evar updates:"
                        putStrLn $ unlines
                            [ "    " ++ show i ++ " -> " ++ show q
                            | (i, q) <- M.toList evars'
                            , q /= M.findWithDefault I i evars
                            ]

                        putStrLn "  rechecking eqs:"
                        putStrLn $ unlines
                            [ "    " ++ show p ++ " ~ " ++ show q
                            | (p, q) <- S.toList eqs'
                            ]

                        case runExcept (S.unions <$> traverse (uncurry conv) (S.toList eqs')) of
                            Left err -> error $ "could not convert: " ++ show err
                            Right cs' -> do
                                putStrLn "  new constraints from conversion:"
                                putStrLn $ unlines ["    " ++ show c | c <- S.toList cs']
                                iter (i+1) (cs' `S.union` cs) ee'

        evars <- iter 1 cs ([], [])

        putStrLn "\n### Final solution ###\n"
        putStrLn $ unlines ["  " ++ show i ++ " -> " ++ show q | (i, q) <- M.toList evars]
        print $ fill evars tm

ex1 :: Term
ex1 =
    Lam (N "Nat" 0) (EV 1) Type $
    Lam (N "Z" 0) (EV 2) (V $ N "Nat" 0) $
    Lam (N "S" 0) (EV 3) (Pi (N "n" 0) (EV 4) (V $ N "Nat" 0) (V $ N "Nat" 0)) $
    App (EV 5) (V $ N "S" 0) (V $ N "Z" 0)

ex2 :: Term
ex2 =
    lam "Nat" 1 Type
    $ lam "Z" 2 (var "Nat")
    $ lam "S" 3 (("_", Q R, var "Nat") ~> var "Nat")
    $ lam "Vect" 5 (("n", Q E, var "Nat") ~> ("a", Q E, Type) ~> Type)
    $ lam "Nil" 8 (("a", EV 9, Type) ~> app (var "Vect") [(10, var "Z"), (11, var "a")])
    $ lam "Cons" 12 (
        ("a", EV 13, Type)
        ~> ("n", Q E, var "Nat")
        ~> ("x", Q R, var "a")
        ~> ("xs", Q R, app (var "Vect") [(17, var "n"), (18, var "a")])
        ~> app (var "Vect") [(19, app (var "S") [(20, var "n")]), (21, var "a")]
    ) $ app (var "Cons")
        [ (22, var "Nat")
        , (23, var "Z")
        , (24, var "Z")
        , (25, app (var "Nil") [(26, var "Nat")])
        ]
  where
    infixr 3 ~>
    lam n ev = Lam (N n 0) (EV ev)
    (n, r, ty) ~> rhs = Pi (N n 0) r ty rhs
    var n = (V $ N n 0)

    app :: Term -> [(Int, Term)] -> Term
    app = foldl (\ap (ev, x) -> App (EV ev) ap x)

ex3 :: Term
ex3 =
    lam "Bool" 1 Type
    $ lam "True" 2 (var "Bool")
    $ lam "False" 3 (var "Bool")
    $ lam "T" 1 Type
    $ lam "C" 4 (("pf", Q I, var "Bool") ~> var "T")  -- if you change this to (Q E), it'll fail to typecheck
    $ lam "U" 6 (("t", Q E, var "T") ~> Type)
    $ lam "D" 7 (("t", Q R, var "T") ~> app (var "U") [(8, var "t")])
    $ lam "g" 9 (("x", Q R, app (var "U") [(10, app (var "C") [(11, var "True")])]) ~> var "Bool")
    $ lam "b" 12 (var "Bool")  -- we don't know what value this bool has but it's irrelevant! :)
    $ app (var "g") [(13, app (var "D") [(14, app (var "C") [(15, var "b")])])]
  where
    infixr 3 ~>
    lam n ev = Lam (N n 0) (EV ev)
    (n, r, ty) ~> rhs = Pi (N n 0) r ty rhs
    var n = (V $ N n 0)

    app :: Term -> [(Int, Term)] -> Term
    app = foldl (\ap (ev, x) -> App (EV ev) ap x)
