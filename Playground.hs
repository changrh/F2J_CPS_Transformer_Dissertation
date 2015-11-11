
module Playground where

import qualified ClosureF as C
import           Core
import           Desugar (desugar)
import           Parser (reader, P(..))
import qualified Src as S
import           System.Exit
import qualified SystemFI as FI
import           TypeCheck (typeCheck)
import qualified OptiUtils (Exp(Hide))
import PrettyUtils
import BackEnd (compileN)
import Simplify  (simplify)

import qualified Language.Java.Syntax as J (Op(..))
import           Language.Java.Pretty (prettyPrint)
import           Text.PrettyPrint.ANSI.Leijen
import           Unsafe.Coerce (unsafeCoerce)

instance Show (Expr t e) where
  show = show . prettyExpr . unsafeCoerce

instance Show (Type t) where
  show = show . prettyType . unsafeCoerce

core2java core =
  do let (cu,_) = compileN "M1" core
     return $ prettyPrint cu

src2test source
  = case reader source of
      PError msg -> do putStrLn msg
                       exitFailure
      POk parsed -> print (pretty parsed)
        -- do
        --   result <- typeCheck parsed
        --   case result of
        --     Left typeError -> do print (pretty typeError)
        --                          exitFailure
        --     Right (_, checked) -> print (pretty checked)

m1src = "package P.k module {rec even (n : Int) : Bool = if n == 0 then True  else odd  (n - 1) and odd  (n : Int) : Bool = if n == 0 then False else even (n - 1)} "

m2src = "import a.m; println \"hello\""

{-
module M1 {

rec even (n : Int) : Bool = if n == 0 then True  else odd  (n - 1)
and
odd  (n : Int) : Bool = if n == 0 then False else even (n - 1);

rec fact (n : Int) : Int = ...;

add (n : Int) (m : Int) = n + m

}

-}

-- m1 :: Expr t e
-- m1 = Module "_"
--        (DefRec
--           ["even", "odd"]
--           [ (S.Fun javaIntS javaBoolS, javaInt `Fun` javaBool)
--           , (S.Fun javaIntS javaBoolS, javaInt `Fun` javaBool)
--           ]
--           (\ids ->
--              [ lam javaInt
--                  (\n -> If (var n `eq` zero) true (App (var (ids !! 1)) (var n `sub` one)))
--              , lam javaInt
--                  (\n -> If (var n `eq` zero) false (App (var (ids !! 0)) (var n `sub` one)))
--              ])
--           (\ids ->
--              (Def "f1" (javaIntS `S.Fun` javaIntS) fact
--                 (\f1 ->
--                    Def
--                      "f2"
--                      (javaIntS `S.Fun` javaIntS)
--                      (lam javaInt (\n -> ((var f1 `App` (var n)) `add` one)))
--                      (\f2 -> Null)))))


--javaIntS = (S.JType (S.JClass "java.lang.Integer"))
--javaBoolS = (S.JType (S.JClass "java.lang.Boolean"))


tailFact :: Expr t e
tailFact
  = fix (\tail_fact acc ->
      lam javaInt (\n ->
        If (var n `eq` zero)
           (var acc)
           (var tail_fact `App` (var acc `mult` var n) `App` (var n `sub` one))))
    javaInt (javaInt `Fun` javaInt)

runTailFact :: Expr t e
runTailFact = App tailFact (Lit (S.Int 300))

testTail :: Expr t e
testTail = App (fix (\f n -> If (var n `eq` zero)
                           one
                           (var f `App` (var n `sub` one)))
               javaInt
               (javaInt `Fun` javaInt)) one

fact :: Expr t e
fact = fix (\f n -> If (var n `eq` zero)
                       one
                       (var n `mult` (var f `App` (var n `sub` one))))
           javaInt
           javaInt

factCPS :: Expr t e
factCPS = App (App (fix (\f n -> 
                lam funtype (\var_1 ->
                   App (fix (\lam_7 var_10 ->
                       App (fix (\lam_8 var_11 -> 
                              Let "Var_12" (var var_10 `eq` var var_11) (\var_12 -> 
                                 App (fix (\lam_1 var_2 ->
                                      If (var var_2)
                                         (App (var var_1) (one) )
                                         (App ( fix (\lam_2 var_3 ->
                                                App (fix (\lam_5 var_7 -> 
                                                     App (fix (\lam_6 var_8 ->
                                                            Let "Var_9" (var var_7 `sub` var var_8) (\var_9 ->
                                                               App (fix (\lam_4 var_6 -> 
                                                                      (App (App (var f) (var var_6) ) 
                                                                        (fix (\lam_3 var_4 -> 
                                                                                  Let "Var_5" (var var_3 `mult` var var_4) (\var_5 -> 
                                                                                        (App (var var_1) (var var_5))
                                                                                    )
                                                                                )
                                                                        javaInt Unit))
                                                                    ) 
                                                               javaInt Unit)
                                                              (var var_9) )
                                                          )
                                                      javaInt Unit)
                                                      one) 
                                                  javaInt Unit)
                                                input)
                                          javaInt Unit )
                                    input ))
                               javaInt Unit)(var var_12)
                            )
                          )
                      javaInt Unit)
                      zero)
                    javaInt Unit)
                 input)
            )
          javaInt Unit) input ) inital_continuation  

testcase1 :: Expr t e
testcase1 = App (fix (\f n -> (App (fix (\f2 n2 -> var n2 `mult` input) javaInt Unit) input) ) javaInt Unit) input  

testcase2 :: Expr t e
testcase2 = App (fix (\f n -> Let "Var_1" (var n `mult` one) (\var_1 -> (App (fix (\f2 n2 -> (var n2 `mult` input) ) javaInt Unit) (var var_1) ) ) ) javaInt Unit )  input

testcase3 :: Expr t e 
testcase3 = App (App (fix (\f n -> lam funtype (\var_1 -> App (var var_1) input) ) javaInt funtype2) input ) inital_continuation

testcase4 :: Expr t e 
testcase4 = App (App (fix (\func n -> 
                              lam funtype (\var_1 -> 
                                ((var func) `App` input) `App` 
                                    (fix (\cont y -> 
                                            App (var y) input) 
                                     funtype Unit) ) ) 
                        javaInt funtype2) 
                      input) 
                inital_continuation



testcase5 :: Expr t e
testcase5 = App (App (fix (\f n ->
                        lam funtype (\k ->
                                        If (var n `eq` zero)
                                           (App (var k) one)
                                           (Let "x" (var n `sub` one) (\x -> 
                                                                         App (App (var f) (var x)) (fix (\cont y ->
                                                                                                            Let "y" (var n `mult` var y) (\z -> App (var k) (var z))
                                                                                                        )
                                                                                                     javaInt Unit
                                                                                                    )  
                                                                      ) 
                                           ) 
                                    )  
                     ) 
                      javaInt funtype2) 
                input) 
            inital_continuation


test1 :: Expr t e
test1 =
  lam javaInt (\f ->
                lam javaInt (\g -> App (var f)
                                   (lam javaInt (\x -> Let "" (App (var g) (var x)) (\t -> var t)))))

tailFactLike :: Expr t e
tailFactLike
  = fix (\tail_fact acc ->
      lam javaInt (\n ->
                    If (var n `eq` zero)
                    (var acc)
                    (var tail_fact `App` (var acc `mult` one) `App` one)))
    javaInt (javaInt `Fun` javaInt)


plus2 :: Expr t e
plus2 = (App (lam (Fun javaInt (Fun javaInt javaInt)) (\e -> (App (App (var e) one) zero)))
             (lam javaInt (\e -> (lam javaInt (\f -> (var e) `mult` (var f))))))

evenOdd :: Expr t e
evenOdd
  = LetRec
      ["even", "odd"]
      [(Fun javaInt javaBool), (Fun javaInt javaBool)]
      (\ids ->
         [ lam javaInt (\n -> If (var n `eq` zero) true  (App (var (ids !! 1)) (var n `sub` one)))
         , lam javaInt (\n -> If (var n `eq` zero) false (App (var (ids !! 0)) (var n `sub` one)))])
      (\ids ->
         App (var (ids !! 1)) magicNumber)


javaBool     = JClass "java.lang.Boolean"
unit         = Unit
zero         = Lit (S.Int 0)
one          = Lit (S.Int 1)
five         = Lit (S.Int 5)
ten          = Lit (S.Int 10)
negOne       = Lit (S.Int (-1))
magicNumber  = Lit (S.Int 42)
true         = Lit (S.Bool True)
false        = Lit (S.Bool False)
input        = Lit (S.Int 300)
x `eq` y     = PrimOp x (S.Compare J.Equal) y
x `neq` y    = PrimOp x (S.Compare J.NotEq) y
x `lt` y     = PrimOp x (S.Compare J.LThan) y
x `bAnd` y    = PrimOp x (S.Logic J.And) y
x `add` y    = PrimOp x (S.Arith J.Add) y
x `sub` y    = PrimOp x (S.Arith J.Sub) y
x `mult` y   = PrimOp x (S.Arith J.Mult) y
inital_continuation = fix (\initial var_0 -> (Lit S.UnitLit)) javaInt Unit
funtype = Fun javaInt Unit
funtype2 = Fun funtype Unit
-- sf2c :: String -> IO (Expr t e)
-- sf2c fname = do
--   path <- {-"/Users/weixin/Project/systemfcompiler/compiler/"-} getCurrentDirectory
--   string <- readFile (path ++ "/" ++ fname)
--   let readSrc = Parser.reader string
--   result <- readSrc `seq` (typeCheck readSrc)
--   case result of
--    Left typeError -> error $ show typeError
--    Right (typ, tcheckedSrc) -> do
--      print tcheckedSrc
--      return (simplify . desugar $ tcheckedSrc)
     -- case n of
     --  1 -> return (peval . simplify . desugar $ tcheckedSrc)
     --  2 -> return (simplify . desugar $ tcheckedSrc)
      -- 3 -> return (desugar $ tcheckedSrc)
      -- _ -> return (peval . desugar $ tcheckedSrc)

mconst =
  (bLam (\a ->
    lam (tVar a) (\x ->
       lam (tVar a) (\y ->
          var x
       )
    )
  ))

notail2 =
  bLam (\a ->
    lam (Fun (tVar a) (Fun (tVar a) (tVar a))) (\f ->
      lam (tVar a) (\x ->
        lam (tVar a) (\y ->
          App (App (var f) (var x)) (App (App (var f) (var y)) (var y)) ))))

program2 = App (App (App (TApp notail2 (JClass "java.lang.Integer")) (TApp mconst (JClass "java.lang.Integer"))) (Lit (S.Int 5))) (Lit (S.Int 6))

notail4 =
  bLam (\a ->
    lam ( Fun (Fun (tVar a) (tVar a)) (Fun (Fun (tVar a) (tVar a)) (tVar a))) (\g ->
      lam (Fun (tVar a) (Fun (tVar a) (tVar a))) (\f ->
        lam (tVar a) (\x ->
          lam (tVar a) (\y ->
            App (App (var g) (App (var f) (var x))) (App (var f) (var y)))))))

summa =
    lam (Fun (JClass "java.lang.Integer") (JClass "java.lang.Integer")) (\x ->
       lam (Fun (JClass "java.lang.Integer") (JClass "java.lang.Integer")) (\y ->
          PrimOp (App (var x) (Lit (S.Int 0))) (S.Arith J.Add) (App (var y) (Lit (S.Int 0)))
       )
    )

program4 = App (App (App (App (TApp notail4 (JClass "java.lang.Integer")) summa) (TApp mconst (JClass "java.lang.Integer"))) (Lit (S.Int 5))) (Lit (S.Int 6))

