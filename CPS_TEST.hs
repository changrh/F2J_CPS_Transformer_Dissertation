{- |
Module      :  CPS_TEST
Description :  Basic translation of FCore to Java
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Johnny.Lin
Stability   :  stable
Portability :  non-portable (MPTC)

This module implements the continuation passing style of FCore. For
more information, please refer to the paper on wiki.
-}


module CPS_TEST where

import           Data.Maybe
import qualified Language.Java.Syntax as J (Op(..))
import           CPS.LambdaF
import           CPS.LambdaK
import           CPS.Transformer
import qualified Src as S
import Text.Printf
import System.CPUTime


time :: IO t -> IO t
time a = do
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10 ** 12)
    printf "Computation time: %0.3f sec\n" (diff :: Double)
    return v

----------------------------------------Evaluator Test--------------------------------------------------

u = let e1 = Annotated_V (N_Var "x") (N_TVar "A") 
        e2 = Annotated_V (N_Var "y") (N_TVar "A") 
     in  N_Fix "f" ["A"] [("x", (N_TVar "A")),("y", (N_TVar "A"))] (N_Let (Declare_O "Z" e1 (S.Arith J.Add) e2) (N_App (Annotated_V (N_Fix "" [] [("k", (N_JClass "Int"))] (N_Halt (Annotated_V (N_Var "k") (N_JClass "Int")))) (N_Forall [] [(N_JClass "Int")] N_Void)) [] [(Annotated_V (N_Var "Z") (N_JClass "Int"))] ))

p = N_App (Annotated_V u (N_Forall ["A"] [(N_TVar "A"),(N_TVar "A")] N_Void)) [(N_JClass "Int")] [(Annotated_V (N_Lit (S.Int 2)) (N_JClass "Int")), (Annotated_V (N_Lit (S.Int 3)) (N_JClass "Int"))]   

u1 = let e1 = Annotated_V (N_Var "x") (N_TVar "A") 
         e2 = Annotated_V (N_Var "y") (N_TVar "A") 
     in  N_Fix "f" ["A"] [("x", (N_TVar "A")),("y", (N_TVar "A"))] (N_Let (Declare_O "Z" e1 (S.Compare J.GThan) e2) (N_App (Annotated_V (N_Fix "" [] [("k", (N_JClass "Int"))] (N_Halt (Annotated_V (N_Var "k") (N_JClass "Int")))) (N_Forall [] [(N_JClass "Int")] N_Void)) [] [(Annotated_V (N_Var "Z") (N_JClass "Int"))] ))

p1 = N_App (Annotated_V u1 (N_Forall ["A"] [(N_TVar "A"),(N_TVar "A")] N_Void)) [(N_JClass "Int")] [(Annotated_V (N_Lit (S.Int 2)) (N_JClass "Int")), (Annotated_V (N_Lit (S.Int 3)) (N_JClass "Int"))]   

u2 = let e1 = Annotated_V (N_Var "x") (N_TVar "A") 
         e2 = Annotated_V (N_Var "y") (N_TVar "A") 
     in  N_Fix 
          "f" 
          ["A"] 
          [("x", (N_TVar "A")),("y", (N_TVar "A")), ("k", (N_Forall [] [(N_JClass "Int")] N_Void))] 
          (N_Let 
            (Declare_O "z" e1 (S.Arith J.Add) e2) 
            (N_App 
              (Annotated_V 
                (N_Var "k")
                (N_Forall [] [(N_JClass "Int")] N_Void)
              ) 
              [] 
              [(Annotated_V (N_Var "Z") (N_JClass "Int"))] 
            )
          )
p2 = N_App 
      (Annotated_V 
        u 
        (N_Forall ["A"] [(N_TVar "A"),(N_TVar "A")] N_Void)
      ) 
      [(N_JClass "Int")] 
      [(Annotated_V (N_Lit (S.Int 2)) (N_JClass "Int")), 
       (Annotated_V (N_Lit (S.Int 3)) (N_JClass "Int")),
       (Annotated_V 
          (N_Fix 
            "" 
            [] 
            [("k", (N_JClass "Int"))] 
            (N_Halt (Annotated_V (N_Var "k") (N_JClass "Int")))
          ) 
          (N_Forall [] [(N_JClass "Int")] N_Void)
        )
      ]   

fact = N_Fix 
        "f"
        []
        [("n", (N_JClass "Int")), ("k", (N_Forall [] [(N_JClass "Int")] N_Void))]
        (N_If
          (Annotated_V (N_Var "n") (N_JClass "Int"))
          (N_App
            (Annotated_V 
                (N_Var "k")
                (N_Forall [] [(N_JClass "Int")] N_Void)
              ) 
            []
            [(Annotated_V (N_Lit (S.Int 1)) (N_JClass "Int"))]
          )
          (N_Let 
            (Declare_O "x" (Annotated_V (N_Var "n") (N_JClass "Int")) (S.Arith J.Sub) (Annotated_V (N_Lit (S.Int 1)) (N_JClass "Int")))
            (N_App
              (Annotated_V (N_Var "f") (N_Forall [] [(N_JClass "Int")] N_Void))
              []
              [(Annotated_V (N_Var "x") (N_JClass "Int")), 
               (Annotated_V
                  (N_Fix 
                    "lam" 
                    [] 
                    [("y", (N_JClass "Int"))]  
                    (N_Let
                      (Declare_O "z" (Annotated_V (N_Var "n") (N_JClass "Int")) (S.Arith J.Mult) (Annotated_V (N_Var "y") (N_JClass "Int")))
                      (N_App
                        (Annotated_V 
                          (N_Var "k")
                          (N_Forall [] [(N_JClass "Int")] N_Void)
                        )  
                        []
                        [(Annotated_V (N_Var "z") (N_JClass "Int"))]
                      )
                    )
                  )
                  (N_Forall [] [(N_JClass "Int")] N_Void)
                )
              ]
            )
          )
        )

fp = N_App
      (Annotated_V
        fact 
        (N_Forall [] [(N_JClass "Int")] N_Void)
      )
      []
      [ (Annotated_V (N_Lit (S.Int 20)) (N_JClass "Int")), 
        (Annotated_V 
          (N_Fix 
            "" 
            [] 
            [("n", (N_JClass "Int"))] 
            (N_Halt (Annotated_V (N_Var "n") (N_JClass "Int")))
          ) 
          (N_Forall [] [(N_JClass "Int")] N_Void)
        )
      ]

red = N_Fix 
        "f"
        []
        [("n", (N_JClass "Int")), ("k", (N_Forall [] [(N_JClass "Int")] N_Void))]
        (N_If 
          (Annotated_V (N_Var "n") (N_JClass "Int"))
          (N_App
            (Annotated_V 
                (N_Var "k")
                (N_Forall [] [(N_JClass "Int")] N_Void)
            ) 
            []
            [(Annotated_V (N_Lit (S.Int 0)) (N_JClass "Int"))]
          )
          (N_Let 
            (Declare_O "z" (Annotated_V (N_Var "n") (N_JClass "Int")) (S.Arith J.Sub) (Annotated_V (N_Lit (S.Int 1)) (N_JClass "Int")))
            (N_App
              (Annotated_V 
                  (N_Var "f")
                  (N_Forall [] [(N_JClass "Int")] N_Void)
              ) 
              []
              [
                (Annotated_V (N_Var "z") (N_JClass "Int")), 
                (Annotated_V (N_Var "k") (N_Forall [] [(N_JClass "Int")] N_Void))
              ]
            )
          )
        )

prog = N_App
        (Annotated_V red (N_Forall [] [(N_JClass "Int")] N_Void))
        []
        [(Annotated_V (N_Lit (S.Int 6)) (N_JClass "Int")), 
         (Annotated_V 
            (N_Fix 
              "" 
              [] 
              [("k", (N_JClass "Int"))] 
              (N_Halt (Annotated_V (N_Var "k") (N_JClass "Int")))
            ) 
            (N_Forall [] [(N_JClass "Int")] N_Void)
          )
        ]

----------------------------------------Transformer Test--------------------------------------------------
----------------------------------------CPS Testing--------------------------------------------------
--Annotated_F (Fix name (n, n_tp) e tp) tp_fix
--Fix String (String, Type) Exp Type
--------------------------TEST CASE 1 -----------------------------------------------------
--lam x:int. x
--main =  let prog = (Fix "Application" ("x", JClass "Int") (Var "x") (JClass "Int"))
--            prog_tp = fromJust (tCheck prog [(" ", Unit)])
--        in  runCPS $ cpsTransProg (Annotated_F  prog prog_tp)
--------------------------TEST CASE 2 -----------------------------------------------------
--lam x:int. (x + 3)
--main =  let prog = (Fix "Add_two_ints" ("x", JClass "Int") (PrimOp (Var "x") (Arith J.Add) (Lit (Int 3))) (JClass "Int"))
--            prog_tp = fromJust (tCheck prog [(" ", Unit)])
--        in runCPS $ cpsTransProg (Annotated_F  prog prog_tp) 
--main = fromJust (tCheck (PrimOp (Lit (Int 3)) (Arith J.Add) (Lit (Int 3))) [(" ", Unit)])
--------------------------TEST CASE 3 -----------------------------------------------------
--main = let e1 = Annotated_V (N_Var "x") (N_TVar "A") 
--           e2 = Annotated_V (N_Var "y") (N_TVar "A") 
--           u  = N_Fix 
--                "f" 
--                ["A"] 
--                [("x", (N_TVar "A")),("y", (N_TVar "A"))] 
--                (N_Let 
--                  (Declare_O "Z" e1 (Arith J.Add) e2) 
--                  (N_App 
--                    (Annotated_V 
--                      (N_Fix 
--                        "" 
--                        [] 
--                        [("k", (N_JClass "Int"))] 
--                        (N_Halt (Annotated_V (N_Var "k") (N_JClass "Int")))
--                      ) 
--                      (N_Forall [] [(N_JClass "Int")] N_Void)
--                    ) 
--                    [] 
--                    [(Annotated_V (N_Var "Z") (N_JClass "Int"))] 
--                  )
--                )
--           p = N_App 
--                (Annotated_V 
--                  u 
--                  (N_Forall ["A"] [(N_TVar "A"),(N_TVar "A")] N_Void)
--                ) 
--                [(N_JClass "Int")] 
--                [(Annotated_V (N_Lit (Int 2)) (N_JClass "Int")), (Annotated_V (N_Lit (Int 3)) (N_JClass "Int"))]
--        in evaluate p [(" ", Annotated_V (N_Lit (Int 3)) (N_JClass "Int") )] [(" ", N_Unit)]


-----------------------------TEST CASE 4 -----------------------------------------------------
--APP (lam x:int. (x + 3)) (Lit Int 3)
--main =  let prog = App (Fix "Add_two_ints" ("x", JClass "Int") (PrimOp (Var "x") (Arith J.Add) (Lit (Int 3))) (JClass "Int")) (Lit (Int 3))
--            prog_tp = fromJust (tCheck prog [(" ", Unit)])
--        --in evaluate (runCPS $ cpsTransProg (Annotated_F  prog prog_tp)) [(" ", Annotated_V (N_Lit (Int 0)) (N_JClass "Int") )] [(" ", N_Unit)]
--        in (runCPS $ cpsTransProg (Annotated_F  prog prog_tp))
-----------------------------TEST CASE 5 -----------------------------------------------------
main = let prog = (Fix "factorial" ("n", JClass "Int") 
                        (If (Var "n")
                            (Lit (S.Int 1))
                            (PrimOp (Var "n") (S.Arith J.Mult) (App (Var "factorial") (PrimOp (Var "n") (S.Arith J.Sub) (Lit (S.Int 1))) ) ) 
                        ) 
                        (JClass "Int")
                  )
           runProg = App prog (Lit (S.Int 1000))
           prog_tp = fromJust (tCheck runProg [(" ", Unit)])
        --in evaluate (runCPS $ cpsTransProg (Annotated_F  runProg prog_tp) ) [(" ", Annotated_V (N_Lit (S.Int 9999)) (N_JClass "Int") )]
        --in fromJust (tCheck prog [(" ", Unit)])
        --in C.prettyExpr $ convertNExp (Map.empty, Map.empty) (runCPS $ cpsTransProg (Annotated_F  runProg prog_tp) )
        --in (runCPS $ cpsTransProg (Annotated_F  runProg prog_tp) )
        in do
            putStrLn "Starting..."
            let result = (evaluate (runCPS $ cpsTransProg (Annotated_F  runProg prog_tp) ) [(" ", Annotated_V (N_Lit (S.Int 9999)) (N_JClass "Int") )])
            time $ result `seq` return ()
            putStrLn "Done."
            print result
-----------------------------TEST CASE 6 -----------------------------------------------------
--main = let prog = (If (Lit (Int 1)) (Lit (Int 2)) (Lit (Int 3)))
--           prog_tp = fromJust (tCheck prog [(" ", Unit)])
--        in evaluate  (runCPS $ cpsTransProg (Annotated_F  prog prog_tp) ) [(" ", Annotated_V (N_Lit (Int 0)) (N_JClass "Int") )] [(" ", N_Unit)]
-----------------------------TEST CASE 7 -----------------------------------------------------
--main = let prog = (Fix "test_if" ("n", JClass "Int") 
--                        (If (PrimOp (Var "n") (Compare J.Equal) (Lit (Int 0)) ) (Lit (Int 1))
--                            (PrimOp (Var "n") (Arith J.Mult) (PrimOp (Var "n") (Arith J.Sub) (Lit (Int 1))) ) 
--                        ) 
--                        (JClass "Int")
--                  )
--           runProg = App prog (Lit (Int 6))
--           prog_tp = fromJust (tCheck runProg [(" ", Unit)])
--        in (runCPS $ cpsTransProg (Annotated_F  prog prog_tp) )
-----------------------------TEST CASE 8 -----------------------------------------------------
--APP (lam x:int. (x + 3 * x)) (Lit Int 3)
--main =  let prog = App (Fix "Add_two_ints" ("x", JClass "Int") (PrimOp (Var "x") (Arith J.Add) (PrimOp (Var "x") (Arith J.Mult) (Lit (Int 3))) ) (JClass "Int")) (Lit (Int 3))
--            prog_tp = fromJust (tCheck prog [(" ", Unit)])
--        in evaluate (runCPS $ cpsTransProg (Annotated_F  prog prog_tp)) [(" ", Annotated_V (N_Lit (Int 0)) (N_JClass "Int") )] [(" ", N_Unit)]
-----------------------------TEST CASE 9 -----------------------------------------------------
--APP (lam x:int. (if (x == 0) (1) (x + 3 * x))) (Lit Int 3)
--main =  let prog = App (Fix "Add_two_ints" ("x", JClass "Int") 
--                          (If (PrimOp (Var "x") (Compare J.Equal) (Lit (Int 0)) ) 
--                            (Lit (Int 0)) 
--                            (PrimOp (Var "x") (Arith J.Add) (PrimOp (Var "x") (Arith J.Mult) (Lit (Int 3))) ) ) 
--                          (JClass "Int")) 
--                  (Lit (Int 0))
--            prog_tp = fromJust (tCheck prog [(" ", Unit)])
--        in evaluate (runCPS $ cpsTransProg (Annotated_F  prog prog_tp)) [(" ", Annotated_V (N_Lit (Int 0)) (N_JClass "Int") )] [(" ", N_Unit)]
-----------------------------TEST CASE 10 -----------------------------------------------------
--APP (lam x:int. (if (x == 0) (1) (x + 3 * x))) (Lit Int 3)
--main =  let prog = App (Fix "Add_two_ints" ("x", JClass "Int") 
--                          (If (PrimOp (Var "x") (Compare J.Equal) (Lit (Int 0)) ) 
--                            (Lit (Int 0)) 
--                            (PrimOp (Var "x") (Arith J.Mult) (App prog (PrimOp (Var "x") (Arith J.Sub) (Lit (Int 1)) ) ) )
--                          ) 
--                          (JClass "Int")) 
--                  (Lit (Int 0))
--            prog_tp = fromJust (tCheck prog [(" ", Unit)])
--        --in evaluate (runCPS $ cpsTransProg (Annotated_F  prog prog_tp)) [(" ", Annotated_V (N_Lit (Int 0)) (N_JClass "Int") )] [(" ", N_Unit)]
--          in runCPS $ cpsTransProg (Annotated_F  prog prog_tp)
-----------------------------TEST CASE 11 -----------------------------------------------------
--f 1 = 1 , f n = f (n-1) 
--main = let prog = (Fix "recursive" ("n", JClass "Int") 
--                        (If (PrimOp (Var "n") (S.Compare J.Equal) (Lit (S.Int 1)) ) 
--                            (Lit (S.Int 1))
--                            (App (Var "recursive") (PrimOp (Var "n") (S.Arith J.Sub) (Lit (S.Int 1))) )
--                        ) 
--                        (JClass "Int")
--                  )
--           runProg = App prog (Lit (S.Int 100))
--           prog_tp = fromJust (tCheck runProg [(" ", Unit)])
--           cpsed_prog = (runCPS $ cpsTransProg (Annotated_F runProg prog_tp) ) 
--        in C.prettyExpr $ convertNExp (Map.empty, Map.empty) (runCPS $ cpsTransProg (Annotated_F  runProg prog_tp) )
        --in evaluate cpsed_prog [(" ", Annotated_V (N_Lit (S.Int 9999)) (N_JClass "Int") )]
        --in print prog
        --in (runCPS $ cpsTransProg (Annotated_F runProg prog_tp) )
        --in fromJust (tCheck runProg [(" ", Unit)])
-----------------------------TEST CASE 12 -----------------------------------------------------
--App (TApp (/\A.\x:A.x) (JClass "Int") ) (Lit (Int 3))
--main = let prog = App (TApp (BLam "A" (Fix "Lam" ("x", TVar "A") (Var "x") (TVar "A") ) ) (JClass "Int")) (Lit (Int 3))
--           prog_tp = fromJust (tCheck prog [(" ", Unit)])
--        in evaluate (runCPS $ cpsTransProg (Annotated_F prog prog_tp) ) [(" ", Annotated_V (N_Lit (Int 0)) (N_JClass "Int") )] [(" ", N_Unit)]

-----------------------------TEST CASE 13 -----------------------------------------------------
--main = let fact = (N_Fix 
--                        "f"
--                        []
--                        [("n", (N_JClass "Int")), ("k", (N_Forall [] [(N_JClass "Int")] N_Void))]
--                        (N_If
--                          (Annotated_V (N_Var "n") (N_JClass "Int"))
--                          (N_App
--                            (Annotated_V 
--                                (N_Var "k")
--                                (N_Forall [] [(N_JClass "Int")] N_Void)
--                              ) 
--                            []
--                            [(Annotated_V (N_Lit (S.Int 1)) (N_JClass "Int"))]
--                          )
--                          (N_Let 
--                            (Declare_O "x" (Annotated_V (N_Var "n") (N_JClass "Int")) (S.Arith J.Sub) (Annotated_V (N_Lit (S.Int 1)) (N_JClass "Int")))
--                            (N_App
--                              (Annotated_V (N_Var "f") (N_Forall [] [(N_JClass "Int"), (N_Forall [] [(N_JClass "Int")] N_Void)] N_Void))
--                              []
--                              [(Annotated_V (N_Var "x") (N_JClass "Int")), 
--                               (Annotated_V
--                                  (N_Fix 
--                                    "lam" 
--                                    [] 
--                                    [("y", (N_JClass "Int"))]  
--                                    (N_Let
--                                      (Declare_O "z" (Annotated_V (N_Var "n") (N_JClass "Int")) (S.Arith J.Mult) (Annotated_V (N_Var "y") (N_JClass "Int")))
--                                      (N_App
--                                        (Annotated_V 
--                                          (N_Var "k")
--                                          (N_Forall [] [(N_JClass "Int")] N_Void)
--                                        )  
--                                        []
--                                        [(Annotated_V (N_Var "z") (N_JClass "Int"))]
--                                      )
--                                    )
--                                  )
--                                  (N_Forall [] [(N_JClass "Int")] N_Void)
--                                )
--                              ]
--                            )
--                          )
--                        )
--                      )

--           fp = (N_App
--                      (Annotated_V
--                        fact 
--                        (N_Forall [] [(N_JClass "Int")] N_Void)
--                      )
--                      []
--                      [ (Annotated_V (N_Lit (S.Int 1000)) (N_JClass "Int")), 
--                        (Annotated_V 
--                          (N_Fix 
--                            "" 
--                            [] 
--                            [("n", (N_JClass "Int"))] 
--                            (N_Halt (Annotated_V (N_Var "n") (N_JClass "Int")))
--                          ) 
--                          (N_Forall [] [(N_JClass "Int")] N_Void)
--                        )
--                      ]
--                     )
--           in do
--                putStrLn "Starting..."
--                let result = (evaluate fp [(" ", Annotated_V (N_Lit (S.Int 9999)) (N_JClass "Int") )])
--                time $ result `seq` return ()
--                putStrLn "Done."
--                print result
                           
-----------------------------TEST CASE 14 -----------------------------------------------------

--main = let prog = N_App 
--                    (Annotated_V 
--                      (N_Fix "Lam_1" [] [("Var_1",N_Forall [] [N_JClass "Int",N_Forall [] [N_JClass "Int"] N_Void] N_Void)] 
--                        (N_App 
--                          (Annotated_V 
--                            (N_Fix "Lam_2" [] [("Var_2",N_JClass "Int")] 
--                              (N_App 
--                                (Annotated_V (N_Var "Var_1") (N_Forall [] [N_JClass "Int",N_Forall [] [N_JClass "Int"] N_Void] N_Void)) 
--                                [] 
--                                [Annotated_V (N_Var "Var_2") (N_JClass "Int"),Annotated_V (N_Fix "Initial_Contination_0" [] [("Var_0",N_JClass "Int")] (N_Halt (Annotated_V (N_Var "Var_0") (N_JClass "Int")))) (N_Forall [] [N_JClass "Int"] N_Void)]
--                              )
--                            ) 
--                            (N_Forall [] [N_JClass "Int"] N_Void)
--                          ) 
--                          [] 
--                          [Annotated_V (N_Lit (Int 10)) (N_JClass "Int")]
--                        )
--                      ) 
--                      (N_Forall [] [N_Forall [] [N_JClass "Int",N_Forall [] [N_JClass "Int"] N_Void] N_Void] N_Void)
--                    ) 
--                    [] 
--                    [Annotated_V 
--                      (N_Fix "factorial" [] [("n",N_JClass "Int"),("Var_3",N_Forall [] [N_JClass "Int"] N_Void)] 
--                        (N_App 
--                          (Annotated_V 
--                            (N_Fix "Lam_10" [] [("Var_13",N_JClass "Int")] 
--                              (N_App 
--                                (Annotated_V 
--                                  (N_Fix "Lam_11" [] [("Var_14",N_JClass "Int")] (
--                                    N_Let (Declare_O "Var_15" (Annotated_V (N_Var "Var_13") (N_JClass "Int")) (Compare J.Equal) (Annotated_V (N_Var "Var_14") (N_JClass "Int"))) 
--                                      N_App 
--                                        (Annotated_V 
--                                          (N_Fix "Lam_3" [] [("Var_4",N_JClass "Bool")] 
--                                            (N_If 
--                                              (Annotated_V (N_Var "Var_4") (N_JClass "Bool")) 
--                                              (N_App 
--                                                (Annotated_V (N_Var "Var_3") (N_Forall [] [N_JClass "Int"] N_Void)) 
--                                                [] 
--                                                [Annotated_V (N_Lit (Int 1)) (N_JClass "Int")]
--                                              ) 
--                                              (N_App 
--                                                (Annotated_V 
--                                                  (N_Fix "Lam_4" [] [("Var_5",N_JClass "Int")] 
--                                                    (N_App 
--                                                      (Annotated_V 
--                                                        (N_Fix "Lam_6" [] [("Var_8",N_Forall [] [N_JClass "Int",N_Forall [] [N_JClass "Int"] N_Void] N_Void)] 
--                                                          (N_App 
--                                                            (Annotated_V 
--                                                              (N_Fix "Lam_8" [] [("Var_10",N_JClass "Int")] 
--                                                                (N_App 
--                                                                  (Annotated_V 
--                                                                    (N_Fix "Lam_9" [] [("Var_11",N_JClass "Int")] 
--                                                                      (N_Let (Declare_O "Var_12" (Annotated_V (N_Var "Var_10") (N_JClass "Int")) (Arith J.Sub) (Annotated_V (N_Var "Var_11") (N_JClass "Int"))) 
--                                                                        (N_App 
--                                                                          (Annotated_V 
--                                                                            (N_Fix "Lam_7" [] [("Var_9",N_JClass "Int")] 
--                                                                              (N_App 
--                                                                                (Annotated_V (N_Var "Var_8") (N_Forall [] [N_JClass "Int",N_Forall [] [N_JClass "Int"] N_Void] N_Void)) 
--                                                                                [] 
--                                                                                [Annotated_V (N_Var "Var_9") (N_JClass "Int"),Annotated_V (N_Fix "Lam_5" [] [("Var_6",N_JClass "Int")] (N_Let (Declare_O "Var_7" (Annotated_V (N_Var "Var_5") (N_JClass "Int")) (Arith J.Mult) (Annotated_V (N_Var "Var_6") (N_JClass "Int"))) (N_App (Annotated_V (N_Var "Var_3") (N_Forall [] [N_JClass "Int"] N_Void)) [] [Annotated_V (N_Var "Var_7") (N_JClass "Int")]))) (N_Forall [] [N_JClass "Int"] N_Void)]
--                                                                              )
--                                                                            ) 
--                                                                            (N_Forall [] [N_JClass "Int"] N_Void)
--                                                                          ) 
--                                                                          [] 
--                                                                          [Annotated_V (N_Var "Var_12") (N_JClass "Int")]
--                                                                        )
--                                                                      )
--                                                                    ) 
--                                                                    (N_Forall [] [N_JClass "Int"] N_Void)
--                                                                  ) 
--                                                                  [] 
--                                                                  [Annotated_V (N_Lit (Int 1)) (N_JClass "Int")]
--                                                                )
--                                                              ) 
--                                                              (N_Forall [] [N_JClass "Int"] N_Void)
--                                                            ) 
--                                                            [] 
--                                                            [Annotated_V (N_Var "n") (N_JClass "Int")]
--                                                          )
--                                                        ) 
--                                                        (N_Forall [] [N_Forall [] [N_JClass "Int",N_Forall [] [N_JClass "Int"] N_Void] N_Void] N_Void)
--                                                      ) 
--                                                      [] 
--                                                      [Annotated_V (N_Var "factorial") (N_Forall [] [N_JClass "Int",N_Forall [] [N_JClass "Int"] N_Void] N_Void)]
--                                                    )
--                                                  ) 
--                                                  (N_Forall [] [N_JClass "Int"] N_Void)
--                                                ) 
--                                                [] 
--                                                [Annotated_V (N_Var "n") (N_JClass "Int")]
--                                              )
--                                            )
--                                          ) 
--                                          (N_Forall [] [N_JClass "Bool"] N_Void)
--                                        ) 
--                                        [] 
--                                        [Annotated_V (N_Var "Var_15") (N_JClass "Int")]
--                                      )
--                                ) 
--                              (N_Forall [] [N_JClass "Int"] N_Void)) [] [Annotated_V (N_Lit (Int 0)) (N_JClass "Int")])) (N_Forall [] [N_JClass "Int"] N_Void)) [] [Annotated_V (N_Var "n") (N_JClass "Int")])) (N_Forall [] [N_JClass "Int",N_Forall [] [N_JClass "Int"] N_Void] N_Void)]
--           in evaluate prog [(" ", Annotated_V (N_Lit (Int 9999)) (N_JClass "Int") )] [(" ", N_Unit)]       



