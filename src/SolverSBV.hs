{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
module SolverSBV (solveSBV) where

import Data.SBV
import Data.Functor
import Data.Generics
import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M

import TT
import Inference

solveSBV :: Constrs -> IO (M.Map Int Q)
solveSBV cs = do
    print =<< optimizeWith defaultSMTCfg{verbose} Lexicographic (goal cs)
    return []
  where
    verbose = True

data Q_ = I_ | E_ | L_ | R_ deriving (Eq, Ord, Data, Read, Show, SymVal, HasKind)

type SQ = SBV Q_

sq :: Q -> Q_
sq I = I_
sq E = E_
sq L = L_
sq R = R_

allQ :: [Q]
allQ = [I, E, L, R]

allQQ :: [(Q, Q)]
allQQ = (,) <$> allQ <*> allQ

declFun :: SymVal a => String -> [a] -> Symbolic (SQ -> SQ -> SBV a)
declFun name table = do
    sequence_
        [ constrain $ f (literal $ sq p) (literal $ sq q) .== (literal r)
        | ((p, q), r) <- zip allQQ table
        ]
    return f
  where
    f = uninterpret name

goal :: Constrs -> Goal
goal cs = do
    add <- declFun "q_add" $ map sq
        [ I, E, L, R
        , E, E, L, R
        , L, L, R, R
        , R, R, R, R
        ]

    let qSum = foldr add (literal I_)

    mul <- declFun "q_mul" $ map sq
        [ I, I, I, I
        , I, E, E, E
        , I, E, L, R
        , I, E, R, R
        ]

    let qProd = foldr mul (literal L_)

    leq <- declFun "q_leq" $ map (== 1)
        [ 1, 1, 0, 1
        , 0, 1, 0, 1
        , 0, 0, 1, 0
        , 0, 0, 0, 1
        ]

    eVars <- traverse (\v -> (v,) <$> evar v) . S.toList $ evars cs
    let eMap = M.fromList eVars
        ev v = eMap M.! v

    forM_ (S.toList $ csEqs cs) $ \(p, q) ->
        constrain $ ev p .== ev q

    forM_ (grp $ csImpls cs) $ \(e, grps) ->
        constrain $ qSum [qProd $ map ev g | g <- grps] `leq` ev e

    minimize "nR" $ cnt R_ eVars
    minimize "nL" $ cnt L_ eVars
    minimize "nE" $ cnt E_ eVars
    minimize "nI" $ cnt I_ eVars  -- just for stats :)
  where
    evar :: Evar -> Symbolic SQ
    evar (EV i) = free $ "e" ++ show i
    evar (Q q)  = pure . literal $ sq q

    grp :: [S.Set Evar :-> Evar] -> [(Evar, [[Evar]])]
    grp is = M.toList $ M.fromListWith (++) [(e, [S.toList gs]) | (gs :-> e) <- is]

    cnt :: Q_ -> [(Evar, SQ)] -> SInteger
    cnt _ [] = literal 0
    cnt q ((_,v):vs) = ite (v .== literal q) 1 0 + cnt q vs

evars :: Constrs -> S.Set Evar
evars Constrs{csImpls, csEqs}
    =  mconcat [ gs <> [e] | gs :-> e <- csImpls ]
    <> mconcat [ [p, q]    | (p, q) <- S.toList csEqs ]
