{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
module SolverSBV (solveSBV) where

import Data.SBV
import Data.Generics
import qualified Data.Set as S
import qualified Data.Map as M

import TT
import Inference

solveSBV :: Constrs -> IO (M.Map Int Q)
solveSBV cs = do
    print =<< optimizeWith defaultSMTCfg{verbose} Lexicographic (goal cs)
    return []
  where
    verbose = False

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

    [x,y,z] <- sBools ["x", "y", "z"]
    constrain $ pbStronglyMutexed [x,y,z]
    maximize "gx" $ 1 * b2i x
    maximize "gy" $ 2 * b2i y
    maximize "gz" $ 3 * b2i z
  where
    b2i b = ite b 1 0 :: SInteger
