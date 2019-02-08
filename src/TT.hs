module TT where

import Pretty

data Name = N String Int | Erased deriving (Eq, Ord, Show)

instance Pretty Name where
    pretty (N s 0) = text s
    pretty (N s i) = text s <> int i
    pretty Erased = text "_"

data Q = I | E | R deriving (Eq, Ord, Show)

instance Pretty Q where
    pretty = text . show

class PrettyR r where
    prettyApp :: r -> Doc
    prettyCol :: r -> Doc

instance PrettyR Q where
    prettyApp q = text "-" <> pretty q <> text "-"
    prettyCol q = text ":" <> pretty q

instance PrettyR () where
    prettyApp () = empty
    prettyCol () = text ":"

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
    deriving (Eq, Ord, Show)

instance Pretty () where
    pretty () = mempty

instance PrettyR r => Pretty (Name, r, TT r) where
    pretty (n, r, ty) = pretty n <+> prettyCol r <+> pretty ty

instance PrettyR r => Pretty (TT r) where
    pretty (V n) = pretty n
    pretty tm@(Lam _ _ (V Erased) _)
        | (ns, rest) <- unLam tm
        = text "\\" <> hsep (map pretty ns) <> dot $$ nest 2 (pretty rest)
    pretty (Lam n r ty rhs) = text "\\" <> pretty (n, r, ty) <> dot $$ nest 2 (pretty rhs)
    pretty (Pi n r ty rhs)  = parens (pretty (n, r, ty)) <+> text "->" <+> pretty rhs
    pretty tm@(App _ _ _)
        | (f, xs) <- unApp [] tm
        = wrap f <+> hsep [prettyApp r <+> wrap x | (r, x) <- xs]
    pretty Type = text "Type"

unLam :: TT r -> ([Name], TT r)
unLam (Lam n r (V Erased) rhs) = case unLam rhs of
    (ns, rest) -> (n:ns, rest)
unLam tm = ([], tm)

unApp :: [(r, TT r)] -> TT r -> (TT r, [(r, TT r)])
unApp acc (App r f x) = unApp ((r,x):acc) f
unApp acc tm = (tm, acc)

wrap :: PrettyR r => TT r -> Doc
wrap tm@Type = pretty tm
wrap tm@(V n) = pretty tm
wrap tm = parens $ pretty tm

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

erase :: Ord r => r -> r -> TT r -> TT ()
erase tyR eR (V n) = V n
erase tyR eR (Lam n r ty rhs)
    | r <= eR = erase tyR eR rhs
    | tyR <= eR = Lam n () (V Erased) $ erase tyR eR rhs
    | tyR >  eR = Lam n () (erase tyR eR ty) $ erase tyR eR rhs
erase tyR eR (Pi n r ty rhs)
    | r <= eR = erase tyR eR rhs
    | tyR <= eR = Pi n () (V Erased) $ erase tyR eR rhs
    | tyR >  eR = Pi n () (erase tyR eR ty) $ erase tyR eR rhs
erase tyR eR (App r f x)
    | r <= eR   = erase tyR eR f
    | otherwise = App () (erase tyR eR f) (erase tyR eR x)
erase tyR eR Type = Type
