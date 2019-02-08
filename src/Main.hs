module Main where

import System.Environment
import Control.Monad.Trans.Except
import qualified Data.Set as S
import qualified Data.Map as M

import TT
import Parser
import Inference
import Solver

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

main :: IO ()
main = getArgs >>= \case
    [fname] -> Parser.readProgram fname >>= \case
        Left err -> error $ show err
        Right tm -> check tm

    _ -> error "usage: itt input.itt"
