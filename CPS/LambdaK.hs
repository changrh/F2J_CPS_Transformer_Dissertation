
module CPS.LambdaK where

import           CPS.LamSrc
import           Data.Maybe (fromJust)
import qualified Language.Java.Syntax as J (Op(..))
import qualified Src as S
import Debug.Trace


-- CPSK Types.
data N_Type = N_TVar Name
            | N_Void
            | N_TupleType [N_Type]
            | N_Forall [Name] [N_Type] N_Type
--------------Forall [Type_Arguments] N_Fun [N_Type] N_Void
--------------Forall must follow the above rule
            | N_Unit
            | N_JClass Name
  deriving (Eq, Show, Read)

type TypeArgs = String

data N_Value = N_Var Name
             | N_Lit S.Lit
             | N_Fix String [TypeArgs] [(Paramter, N_Type)] N_Exp
           ----Fix x [a] (X1:T1,.....Xn:Tn). e
           ----TypePara is a type argument used in N_Type in the binder
           ----Parameter is a String, which indicates a corresponding N_Value in the Fix Body  
             | N_Tuple [Annotated_V]
  deriving (Eq, Show)

------------------In Declaration N_Value should be N_Var Name---------------
data Declaration = Declare_V String  Annotated_V
            ------- x = v  here x is a N_Var
                 | Declare_T String Int Annotated_V
            ------- x = Proj Int Tuple [N_Value]
                 | Declare_O String Annotated_V S.Operator Annotated_V
            ------- x = v1 Op v2
  deriving (Eq, Show)
data N_Exp = N_Let Declaration N_Exp
        -----Let d in e 
           | N_If Annotated_V N_Exp N_Exp
        -----If (v, e1, e2)
           | N_App Annotated_V [N_Type] [Annotated_V]
        -----N_App Fix [Type_Arguments] [correspond to Fix Parameters]
        -----This is a hybrid of App and TApp N_App N_Value [String] is a TApp for Fix
        -----And N_App N_Value [] [N_Value] is an App  
           | N_Halt Annotated_V
        -----Halt [T] V   
  deriving (Eq, Show)

data Annotated_V = Annotated_V N_Value N_Type
  deriving (Eq, Show)


---------------------------------------- Evaluator --------------------------------------------------
type Env = [(String, Annotated_V)]

-- IMPORTANT: Only EXP can be evaluated, others cannot

evaluate :: N_Exp -> Env -> N_Value

evaluate (N_Let dec body) env = evaluate body newEnv
  where newEnv = case dec of 
                  -- av cannot be (Fix ...) since there is no App outside to provide arguments

                  Declare_V n av -> (n, (deReferenceAV av env)):env
                  Declare_T n idx av -> (n, (takeByID idx (deReferenceAV av env))):env                  
                  Declare_O n av1 op av2 -> (n, (calculate op (de_annotate (deReferenceAV av1 env)) (de_annotate (deReferenceAV av2 env)) )):env

        takeByID idx (Annotated_V (N_Tuple xs) (N_TupleType ys)) = Annotated_V (de_annotate (xs!!idx)) (ys!!idx)
        takeByID _ _ = error "Not a proper tuple format"
 
evaluate (N_If av e1 e2) env = if eval_bool (deReferenceAV av env) then evaluate e1 env 
                                                                   else evaluate e2 env 

evaluate (N_App av ts args) env = eval_app (funcDeRef av env) where   

  eval_app func@(Annotated_V (N_Fix fn tns pts body) t) = evaluate body newEnv 
        where newEnv = case lookup fn env of 
                          Nothing -> [(fn, func)] ++ (zip (map fst pts) (map ((flip deReferenceAV) env) args)) ++ env
                          _ -> (zip (map fst pts) (map ((flip deReferenceAV) env) args)) ++ env
  
  eval_app _ = error (show av ++ "is not defined or is not a function")

evaluate (N_Halt av) env = de_annotate (deReferenceAV av env)

eval_bool :: Annotated_V -> Bool
eval_bool (Annotated_V (N_Lit (S.Bool v)) t) = v
eval_bool (Annotated_V (N_Lit (S.Int v)) t) = if v == 0 then True else False
eval_bool av = error ("Value " ++ show av ++ " is not a proper predicate")

de_annotate :: Annotated_V -> N_Value
de_annotate (Annotated_V v t) = v
de_annotate av = error ("Unknown value" ++ show av)

funcDeRef :: Annotated_V -> Env -> Annotated_V
funcDeRef (Annotated_V (N_Var f) t) env                 = case lookup f env of
                                                                Nothing -> error ("Undefined Function " ++ f)
                                                                Just av -> funcDeRef av env
funcDeRef av env                                        = av                                                               

deReferenceAV :: Annotated_V -> Env -> Annotated_V
deReferenceAV (Annotated_V (N_Lit v) t) env                = Annotated_V (N_Lit v) t
deReferenceAV (Annotated_V (N_Var x) t) env                = case lookup x env of
                                                              Nothing -> Annotated_V (N_Var x) t
                                                              --Just av -> av
                                                              Just av -> deReferenceAV av env
deReferenceAV (Annotated_V (N_Fix fn targs pts exp) t) env = 
    case lookup fn env of
      Nothing -> Annotated_V (N_Fix fn targs pts (deReferenceExp exp env)) t
      Just av -> Annotated_V (N_Fix fn targs pts exp) t
deReferenceAV (Annotated_V (N_Tuple avs) t) env            = Annotated_V (N_Tuple (map ((flip deReferenceAV) env) avs)) t
deReferenceAV v _                                          = error ("Value " ++ show v ++ "cannot be de-referenced") 

deReferenceExp :: N_Exp -> Env -> N_Exp
deReferenceExp (N_Let dec exp) env    = N_Let (deReferenceDec dec env) (deReferenceExp exp env)
deReferenceExp (N_If av e1 e2) env    = N_If (deReferenceAV av env) (deReferenceExp e1 env) (deReferenceExp e2 env)
deReferenceExp (N_App av ts args) env = N_App (deReferenceAV av env) ts (map ((flip deReferenceAV) env) args)
deReferenceExp (N_Halt av) env        = N_Halt av 

deReferenceDec :: Declaration -> Env -> Declaration
deReferenceDec (Declare_V n av) env         = Declare_V n (deReferenceAV av env)
deReferenceDec (Declare_T n idx av) env     = Declare_T n idx (deReferenceAV av env)
deReferenceDec (Declare_O n av1 op av2) env = Declare_O n (deReferenceAV av1 env) op (deReferenceAV av2 env)

calculate :: S.Operator -> N_Value -> N_Value -> Annotated_V
calculate (S.Arith J.Add) (N_Lit (S.Int a)) (N_Lit (S.Int b))      = Annotated_V (N_Lit (S.Int (a + b))) (N_JClass "Int")
calculate (S.Arith J.Sub) (N_Lit (S.Int a)) (N_Lit (S.Int b))      = Annotated_V (N_Lit (S.Int (a - b))) (N_JClass "Int") 
calculate (S.Arith J.Mult) (N_Lit (S.Int a)) (N_Lit (S.Int b))     = Annotated_V (N_Lit (S.Int (a * b))) (N_JClass "Int") 
--calculate (Arith J.Div) (N_Lit (Int a)) (N_Lit (Int b)) = Annotated_V (N_Lit (Int (a 'div' b))) (N_JClass "Integer") 
--calculate (Arith J.Rem) (N_Lit (Int a)) (N_Lit (Int b)) = Annotated_V (N_Lit (Int (a % b))) (N_JClass "Integer")
calculate (S.Compare J.GThan) (N_Lit (S.Int a)) (N_Lit (S.Int b))  = Annotated_V (N_Lit (S.Bool (a > b))) (N_JClass "Bool")  
calculate (S.Compare J.GThanE) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Annotated_V (N_Lit (S.Bool (a >= b))) (N_JClass "Bool") 
calculate (S.Compare J.LThan) (N_Lit (S.Int a)) (N_Lit (S.Int b))  = Annotated_V (N_Lit (S.Bool (a < b))) (N_JClass "Bool") 
calculate (S.Compare J.LThanE) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Annotated_V (N_Lit (S.Bool (a <= b))) (N_JClass "Bool") 
calculate (S.Compare J.Equal) (N_Lit (S.Int a)) (N_Lit (S.Int b))  = Annotated_V (N_Lit (S.Bool (a == b))) (N_JClass "Bool")     
