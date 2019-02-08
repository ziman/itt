module Solver where

import Data.Foldable
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.Trans.Except

import TT
import Inference

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