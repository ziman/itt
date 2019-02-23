module SolverPure (solvePure) where

import TT
import Inference

import Control.Monad.Trans.Except
import qualified Data.Map as M
import qualified Data.Set as S

solvePure :: Constrs -> Except String (M.Map Int Q)
solvePure Constrs{csImpls, csEqs} = undefined
  where
    impls = map (\(gs :-> v) -> S.map repr gs :-> repr v) csImpls
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
