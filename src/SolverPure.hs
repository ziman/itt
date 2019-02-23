module SolverPure (solvePure) where

import TT
import Inference

import Control.Monad.Trans.Except
import qualified Data.Map as M
import qualified Data.Set as S

rig0 :: Q
rig0 = I

rig1 :: Q
rig1 = L

add :: Q -> Q -> Q
add _ _ = I

mul :: Q -> Q -> Q
mul _ _ = I

leq :: Q -> Q -> Bool
leq _ _ = True

iter :: M.Map Int Q -> M.Map Evar [S.Set Evar] -> Except String (M.Map Int Q)
iter vals cs = do
    vals' <- run vals $ M.toList cs
    if vals' == vals
        then return vals
        else iter vals' cs

eval :: M.Map Int Q -> [S.Set Evar] -> Q
eval vals = foldr (add . foldr (mul . val) rig1) rig0
  where
    val (EV i) = vals M.! i
    val (Q q) = q

run :: M.Map Int Q -> (Evar, [S.Set Evar]) -> Except String (M.Map Int Q)
run vals [] = vals
run vals ((Q q, gss) : impls)
    | eval vals gss `leq` q = run vals impls
    | otherwise = throwE $ "cannot solve " ++ show (gss, q)
run vals ((EV i, gss) : impls)
    | q <- eval vals gss
    = case M.lookup i vals of
        Nothing -> run (M.insert i q vals) impls
        Just q'
            | q' `leq` q -> run (M.insert i q vals) impls
            | q `leq` q' -> run vals impls  -- nothing to do
            | otherwise  -> throwE $ "incomparable bump of evar " ++ show i ++ " between " ++ show (q', q)

solvePure :: Constrs -> Except String (M.Map Int Q)
solvePure Constrs{csImpls, csEqs} = iter M.empty implsGrouped
  where
    implsGrouped = M.fromListWith (++)
        [ (repr v, [S.map repr gs])
        | (gs :-> v) <- csImpls
        ]
    repr = (reprMap M.!)
    reprMap = M.fromList [(ev, head $ S.toList (gGroups M.! g)) | (ev, g) <- M.toList gIndex]
    Groups{gIndex, gGroups} = foldr merge noGroups $ S.toList csEqs

data Groups = Groups
    { gIndex  :: M.Map Evar Int
    , gGroups :: M.Map Int (S.Set Evar)
    }

noGroups :: Groups
noGroups = Groups M.empty M.empty

merge :: (Evar, Evar) -> Groups -> Groups
merge (u, v) Groups{gIndex, gGroups} = case (M.lookup u gIndex, M.lookup v gIndex) of
    (Nothing, Nothing) -> let g = M.size gGroups in Groups
        { gIndex = M.insert u g $ M.insert v g gIndex
        , gGroups = M.insert g [u, v] gGroups
        }

    (Just g, Nothing) -> Groups
        { gIndex = M.insert v g gIndex
        , gGroups = M.insertWith S.union g [v] gGroups
        }

    (Nothing, Just g) -> Groups
        { gIndex  = M.insert u g gIndex
        , gGroups = M.insertWith S.union g [u] gGroups
        }

    (Just gu, Just gv)
        | Just gus <- M.lookup gu gGroups
        , Just gvs <- M.lookup gv gGroups
        -> if S.size gus < S.size gvs
            then Groups
                { gIndex = M.fromList [(x, gv) | x <- S.toList gus] `M.union` gIndex
                , gGroups = M.insertWith S.union gv gus $ M.delete gu gGroups
                }
            else Groups
                { gIndex = M.fromList [(x, gu) | x <- S.toList gvs] `M.union` gIndex
                , gGroups = M.insertWith S.union gu gvs $ M.delete gv gGroups
                }

    _ -> error "impossible"
