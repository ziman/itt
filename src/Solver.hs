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
    = CantConvert Backtrace Term Term
    deriving (Eq, Ord)

instance Show ConvErr where
    show (CantConvert (BT bt) p q) = "With backtrace:\n" ++ unlines (map ("  "++) $ reverse bt)
        ++ "!! can't convert " ++ show p ++ " ~ " ++ show q

conv :: Backtrace -> Term -> Term -> Except ConvErr Constrs
conv bt (V n) (V n') | n == n' = return mempty
conv bt (Lam n r ty rhs) (Lam n' r' ty' rhs') = do
    tycs  <- conv bt ty ty'
    rhscs <- conv bt rhs $ subst n' (V n) rhs'
    return $ tycs <> rhscs <> mempty { csEqs = [(r, r')] }

conv bt (Pi n r ty rhs) (Pi n' r' ty' rhs') = do
    tycs  <- conv bt ty ty'
    rhscs <- conv bt rhs $ subst n' (V n) rhs'
    return $ tycs <> rhscs <> mempty { csEqs = [(r, r')] }

conv bt (App r f x) (App r' f' x') = do
    fcs <- conv bt f f'
    return $ fcs <> mempty
        { csEqs = [(r, r')]
        , csConvs =  [[r] :-> (bt, x, x')]
        }

conv _bt Type Type = return mempty

conv bt p q = throwE $ CantConvert bt p q

val :: M.Map Int Q -> Evar -> Q
val evars (EV i) = M.findWithDefault I i evars
val _ (Q q)  = q

vals :: Foldable t => M.Map Int Q -> t Evar -> Q
vals evars = fold . map (val evars) . toList
