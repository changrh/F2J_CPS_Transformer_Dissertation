{- |
Module      :  CPS.LambdaK
Description :  Basic translation of FCore to Java
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Johnny.Lin
Stability   :  stable
Portability :  non-portable (MPTC)

This module implements the continuation passing style of FCore. For
more information, please refer to the paper on wiki.
-}

module CPS.LambdaK where

import           CPS.LamSrc
import           Data.Maybe (fromJust)
import qualified Language.Java.Syntax as J (Op(..))
import qualified Src as S


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
type NTEnv = [(String, N_Type)]

evaluate :: N_Exp -> Env -> NTEnv -> Maybe N_Value

evaluate (N_Let dec body) env tenv = evaluate body newEnv tenv
  where newEnv = case dec of 
                  Declare_V n v -> (n, v):env
                  --Declare_T n idx tuple -> (n, (fromJust (eval_tuple idx tuple))):env                  
                  Declare_O n (Annotated_V v1 t1) op (Annotated_V v2 t2) -> (n, (fromJust (eval_op op (eval_value v1 env) (eval_value v2 env)))):env
                 
evaluate (N_If av e1 e2) env tenv = 
    if fromJust (eval_bool av) then evaluate e1 env tenv
                               else evaluate e2 env tenv where

      eval_bool (Annotated_V (N_Var x) t) = 
        case lookup x env of
          Nothing -> error "Lookup Error2!"
          Just av -> eval_bool av

      eval_bool (Annotated_V (N_Lit (S.Bool bv)) bt) = Just bv

      eval_bool (Annotated_V (N_Lit (S.Int i)) it) = 
        if i == 0 then Just True else Just False

      eval_bool _ = Nothing

evaluate (N_App av ts avs) env tenv = eval_app av where   

  eval_app (Annotated_V (N_Var n) t) = 
    case lookup n env of
      Nothing -> error (show env++n)
      Just av' -> eval_app av'

  eval_app func@(Annotated_V (N_Fix f tns pts body) t) = evaluate body newEnv newTEnv
        where newEnv = case lookup f env of 
                          Nothing -> [(f, func)] ++ (zip (map fst pts) (map subst_av avs)) ++ env
                          _ -> (zip (map fst pts) (map subst_av avs)) ++ env
              newTEnv = (zip tns ts) ++ tenv

              subst_exp (N_Let dec body') = (N_Let (subst_dec dec) (subst_exp body'))
              subst_exp (N_If av e1 e2) = (N_If (subst_av av) (subst_exp e1) (subst_exp e2))
              subst_exp (N_App av ts avs) = (N_App (subst_av av) ts avs)
              subst_exp other = other

              subst_dec (Declare_V n av) = (Declare_V n (subst_av av))
              subst_dec (Declare_T s n av) = (Declare_T s n (subst_av av))
              subst_dec (Declare_O n av1 op av2) = (Declare_O n (subst_av av1) op (subst_av av2))

              subst_av var@(Annotated_V (N_Var n) t) = 
                case lookup n env of 
                  Nothing -> var
                  Just av -> subst_av av
              subst_av (Annotated_V (N_Lit n) t) = (Annotated_V (N_Lit n) t) 
              subst_av (Annotated_V (N_Fix n tpns pns exp) t) = (Annotated_V (N_Fix n tpns pns (subst_exp exp)) t)
              subst_av other = other --Patten for tuple is needed 
              

evaluate (N_Halt (Annotated_V v t)) env tenv = Just (eval_value v env) where


--eval_tuple :: Int -> Annotated_V -> Maybe Annotated_V
--eval_tuple idx (Annotated_V (N_Tuple xs) (N_TupleType ys)) = Just (Annotated_V (xs!!idx) (ys!!idx))
--eval_tuple _ _ = Nothing

eval_value :: N_Value -> Env -> N_Value
eval_value (N_Var x) env =
  case lookup x env of
    Nothing -> error "Lookup Error3!"
    Just (Annotated_V v t) -> eval_value v env
eval_value (N_Lit v) env = N_Lit v
eval_value _ _ = error "Unknow value"

eval_op :: S.Operator -> N_Value -> N_Value -> Maybe Annotated_V
eval_op (S.Arith J.Add) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Just (Annotated_V (N_Lit (S.Int (a + b))) (N_JClass "Int"))
eval_op (S.Arith J.Sub) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Just (Annotated_V (N_Lit (S.Int (a - b))) (N_JClass "Int")) 
eval_op (S.Arith J.Mult) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Just (Annotated_V (N_Lit (S.Int (a * b))) (N_JClass "Int")) 
--eval_op (Arith J.Div) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Int (a 'div' b))) (N_JClass "Integer")) 
--eval_op (Arith J.Rem) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Int (a % b))) (N_JClass "Integer"))  
eval_op (S.Compare J.GThan) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Just (Annotated_V (N_Lit (S.Bool (a > b))) (N_JClass "Bool"))  
eval_op (S.Compare J.GThanE) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Just (Annotated_V (N_Lit (S.Bool (a >= b))) (N_JClass "Bool")) 
eval_op (S.Compare J.LThan) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Just (Annotated_V (N_Lit (S.Bool (a < b))) (N_JClass "Bool")) 
eval_op (S.Compare J.LThanE) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Just (Annotated_V (N_Lit (S.Bool (a <= b))) (N_JClass "Bool")) 
eval_op (S.Compare J.Equal) (N_Lit (S.Int a)) (N_Lit (S.Int b)) = Just (Annotated_V (N_Lit (S.Bool (a == b))) (N_JClass "Bool"))     







