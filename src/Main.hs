module Main where

import System.Environment
import Control.Monad.Trans.Except
import qualified Data.Set as S
import qualified Data.Map as M

import TT
import Parser
import Inference
import Solver
import SolverSBV
import SolverPure
import Pretty

check :: Term -> IO ()
check tm = case infer tm of
    Left err -> print err
    Right (ty, cs) -> do
        putStrLn "### Inferred type ###\n"
        printP tm
        putStrLn $ "\n  : " ++ prettyShow ty
        putStrLn ""
        putStrLn "### Constraints ###\n"
        putStrLn $ unlines ["  " ++ show c | c <- S.toList $ csConvs cs]
        putStrLn $ unlines ["  " ++ show c | c <- csImpls cs]
        putStrLn $ unlines ["  " ++ show c | c <- S.toList $ csEqs cs]

        putStrLn "### Solving ###\n"
        let iter :: Int -> Constrs -> (M.Map Int Q, S.Set (Backtrace, TT Evar, TT Evar)) -> IO (M.Map Int Q)
            iter i cs ee@(evars, eqs) = do
                putStrLn $ "-> iteration " ++ show i
                let evars' = case runExcept (solvePure cs) of
                        Left err  -> error $ "no solution found: " ++ err
                        Right evs -> evs
                let eqs' = S.fromList
                            [(bt, p, q)
                            | (gs :-> (bt, p, q)) <- S.toList $ csConvs cs
                            , vals evars' gs > I
                            ]
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
                            | (_bt, p, q) <- S.toList eqs'
                            ]

                        case runExcept (mconcat <$> traverse (\(bt,p,q) -> conv bt p q) (S.toList eqs')) of
                            Left err -> error $ "could not convert: " ++ show err
                            Right cs' -> do
                                putStrLn "  new constraints from conversion:"
                                putStrLn $ unlines ["    " ++ show c | c <- S.toList $ csConvs cs']
                                putStrLn $ unlines ["    " ++ show c | c <- csImpls cs']
                                putStrLn $ unlines ["    " ++ show p ++ " = " ++ show q | (p, q) <- S.toList $ csEqs cs']
                                iter (i+1) (cs' <> cs) ee'

        evars <- iter 1 cs ([], [])

        putStrLn "\n### Final solution ###\n"
        putStrLn $ unlines ["  " ++ show i ++ " -> " ++ show q | (i, q) <- M.toList evars]

        putStrLn "### Fully annotated program ###\n"
        let solution = fill evars tm
        printP solution

        putStrLn "\n### Erase: irrelevant data ###\n"
        printP (erase I solution)

        putStrLn "\n### Erase: non-runtime data ###\n"
        printP (erase E solution)

main :: IO ()
main = getArgs >>= \case
    [fname] -> Parser.readProgram fname >>= \case
        Left err -> error $ show err
        Right tm -> check tm

    _ -> error "usage: itt input.tt"
