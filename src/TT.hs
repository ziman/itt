module TT where

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
