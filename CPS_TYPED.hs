{- |
Module      :  CPS
Description :  Basic translation of FCore to Java
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Johnny.Lin
Stability   :  stable
Portability :  non-portable (MPTC)

This module implements the continuation passing style of FCore. For
more information, please refer to the paper on wiki.
-}


module CPS where

import           Data.Maybe (fromJust)
import qualified Language.Java.Syntax as J (Op(..))

type Name      = String
type ClassName = String

-------------SystemF Types-------------------------------------------------
data Type
  = TVar Name
  | JClass ClassName
  | Unit
  | Fun Type Type
  | Forall Name Type
  | TupleType [Type]
  deriving (Eq, Show, Read)


data Lit -- Data constructor names match Haskell types
  = Int Integer
  | String String
  | Bool Bool
  | Char Char
  | UnitLit
  deriving (Eq, Show)

data Operator = Arith J.Op | Compare J.Op | Logic J.Op deriving (Eq, Show)


----------------SystemF Expressions-----------------------------------------
data Exp
  = Var String
  | Lit Lit
  | Lam (String, Type) Exp
  | App Exp Exp
  | BLam String Exp
  | TApp Exp Type
  | PrimOp Exp Operator Exp
  | If Exp Exp Exp
  | Proj Int Exp
  | Tuple [Exp]
  | Fix String (String, Type) Exp Type
  | Let (String, Type) Exp Exp
  deriving (Eq, Show)

------------------------All The Type Checker For SystemF----------------------

type TEnv = [(String, Type)]

substitute :: Type -> (String, Type) -> Type
substitute (TVar x) (n, t) = if x == n then t else TVar x
substitute (Forall n tp) (n1, t) = if n == n1 then substitute tp (n1, t) else (Forall n tp)
substitute (Fun t1 t2) (n, t) = Fun (substitute t1 (n, t)) (substitute t2 (n, t))
--substitute (TupleType (x:xs)) (n, t) = TupleType ((substitute x (n ,t)):[(substitute (TupleType xs) (n, t))])
substitute (TupleType (x:xs)) (n, t) = TupleType ((substitute x (n ,t)):(subList xs (n, t)))
  where subList list (n, t) = case list of
                                [] -> []
                                (y:ys) -> (substitute y (n ,t)):subList ys (n, t)
substitute (JClass x) (n, t) = if x == n then t else JClass x
substitute (Unit) (n, t) = Unit   

tbinary :: Operator -> Type -> Type -> Maybe Type
tbinary (Arith _) (JClass t1) (JClass t2)  =  Just (JClass t1)
tbinary (Compare _) (JClass t1)  (JClass t2) = Just (JClass "Bool")
tbinary (Logic _) (JClass "Bool")  (JClass "Bool")   = Just (JClass "Bool")
tbinary _ _ _ = Nothing

tCheck :: Exp -> TEnv -> Maybe Type
tCheck (Var n) tenv             = lookup n tenv

tCheck (Lit n) tenv             = 
  case n of 
    UnitLit -> Just Unit
    Char t -> Just (JClass "Char")
    Int t -> Just (JClass "Int")
    String t -> Just (JClass "String")
    Bool t -> Just (JClass "Bool")
    _ -> Nothing
tCheck (App e1 e2) tenv           = 
  case (tCheck e1 tenv, tCheck e2 tenv) of
    (Just t1, Just t2) -> case t1 of 
                            Fun inType outType -> if inType == t2 then Just (outType) else Nothing
                            _ -> Nothing
    _ -> Nothing

tCheck (Lam (n, t) e) tenv      = 
  case tCheck e ((n,t) : tenv) of 
      Just t1 -> Just (Fun t t1)
      _ -> Nothing 

tCheck (BLam n e) tenv          = 
  case tCheck e tenv of 
    Just t1 -> Just (Forall n t1)
    _ -> Nothing

tCheck (Let (n, t1) e body) tenv = Just Unit

tCheck (TApp e t) tenv          = Just (substitute (Forall alpha tp) (alpha, t))
  where Forall alpha tp = fromJust (tCheck e tenv)

tCheck (PrimOp e1 op e2) tenv   =
  case (tCheck e1 tenv, tCheck e2 tenv) of
    (Just t1, Just t2) -> tbinary op t1 t2
    _ -> Nothing

tCheck (If p e1 e2) tenv        =
  case tCheck p tenv of
    Nothing -> Nothing
    Just (JClass "Bool") -> case tCheck e1 tenv of 
                              Nothing -> Nothing
                              Just t1 -> if (Just t1 == (tCheck e2 tenv)) then Just t1 else Nothing
    _ -> Nothing

tCheck (Proj index e) tenv        = 
  case e of 
    Tuple xs -> tCheck (xs !! index) tenv
    _ -> Nothing


tCheck (Tuple (x:xs)) tenv      =  let out = TupleType (fromJust((tCheck x tenv)):subList xs tenv)
                                       subList xs tenv = case xs of
                                                                [] -> []
                                                                (y:ys) -> fromJust(tCheck y tenv) : (subList ys tenv) 
                                   in 
                                      Just out

tCheck (Fix n1 (n2, t1) e t2) tenv  = Just (Fun t1 t2)

data Annotated_F = Annotated_F Exp Type

--------------------------------Define CPSK data type ------------------------------------------------

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
type Paramter = String
type TypeArgs = String

data N_Value = N_Var Name
             | N_Lit Lit
             | N_Fix String [TypeArgs] [(Paramter, N_Type)] N_Exp
           ----Fix x [a] (X1:T1,.....Xn:Tn). e
           ----TypePara is a type argument used in N_Type in the binder
           ----Parameter is a String, which indicates a corresponding N_Value in the Fix Body  
             | N_Tuple [N_Value]
  deriving (Eq, Show)

------------------In Declaration N_Value should be N_Var Name---------------
data Declaration = Declare_V String  Annotated_V
            ------- x = v  here x is a N_Var
                 | Declare_T String Int Annotated_V
            ------- x = Proj Int Tuple [N_Value]
                 | Declare_O String Annotated_V Operator Annotated_V
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
------------------------------CPS Transformation from SystemF to CSPK----------------------------------

cpsTransType :: Type -> N_Type
cpsTransType (TVar name)           = N_TVar name

cpsTransType (JClass name)         = N_JClass name
cpsTransType  Unit                 = N_Unit
cpsTransType (Fun t1 t2)           = N_Forall [] [cpsTransType(t1), cpsTransCont(t2)] N_Void 
cpsTransType (Forall name tp)      = N_Forall [name] [cpsTransCont(tp)] N_Void
cpsTransType (TupleType (x:xs))    = N_TupleType (cpsTransType(x) : subList xs)
                                    where subList xs = case xs of 
                                                        [] -> []
                                                        (y:ys) -> (cpsTransType y) : (subList ys)

cpsTransCont :: Type -> N_Type
cpsTransCont tp = N_Forall [] [cpsTransType(tp)] N_Void

cpsTransExp :: Annotated_F -> Annotated_V -> N_Exp
cpsTransExp (Annotated_F (Var name) tp) cont                   = N_App cont [] [(Annotated_V (N_Var name) (cpsTransType tp))]  
cpsTransExp (Annotated_F (Lit n) tp) cont                      = N_App cont [] [(Annotated_V (N_Lit n) (cpsTransType tp))] 
cpsTransExp (Annotated_F (BLam name e) tp) cont                = case tp of 
                                                                    Forall n t -> (let c_tp = cpsTransCont t
                                                                                       exp_tp = cpsTransType tp
                                                                                       exp = N_Fix "BLam" [name] [("c", c_tp)] (cpsTransExp (Annotated_F e t) (Annotated_V (N_Var "c") c_tp))                                                                                  
                                                                                  in N_App cont [] [(Annotated_V exp exp_tp)] )
cpsTransExp (Annotated_F (App e1 e2) tp) cont                  = let e1_tp = fromJust (tCheck e1 [(" ", Unit)])
                                                                     e2_tp = fromJust (tCheck e2 [(" ", Unit)])
                                                                     u1    = Annotated_F e1 e1_tp
                                                                     u2    = Annotated_F e2 e2_tp
                                                                     u1_cont = cpsTransCont e1_tp
                                                                     u2_cont = cpsTransCont e2_tp
                                                                     x1_tp   = cpsTransType e1_tp
                                                                     x2_tp   = cpsTransType e2_tp
                                                                     lam_x1  = N_Fix "lam_x1" [] [("x1", x1_tp)] (cpsTransExp u2 (Annotated_V lam_x2 u2_cont) )
                                                                     lam_x2  = N_Fix "lam_x2" [] [("x2", x2_tp)] (N_App (Annotated_V (N_Var "x1") x1_tp) [] [(Annotated_V (N_Var "x2") x2_tp), cont])
                                                                    in (cpsTransExp u1 (Annotated_V lam_x1 u1_cont) )
cpsTransExp (Annotated_F (Fix name (n, n_tp) e tp) tp_fix) cont = let x1_tp  = cpsTransType n_tp
                                                                      c_tp   = cpsTransCont tp
                                                                      fix_tp = cpsTransType tp_fix
                                                                      fix_trans = N_Fix name [] [("x1", x1_tp),("c", c_tp)] (cpsTransExp (Annotated_F e tp) (Annotated_V (N_Var "c") c_tp))
                                                                  in (N_App cont [] [(Annotated_V fix_trans fix_tp)])
cpsTransExp (Annotated_F (TApp e ay_tp) tp) cont                = let e_tp = fromJust (tCheck e [("", Unit)])
                                                                      x_tp = cpsTransType e_tp
                                                                      ay_tran_tp = cpsTransType ay_tp
                                                                      lam_x = N_Fix "lam_x" [] [("x", x_tp)] (N_App (Annotated_V (N_Var "x") x_tp) [ay_tran_tp] [cont])
                                                                      lam_x_tp = cpsTransType tp                                                     
                                                                  in cpsTransExp (Annotated_F e e_tp) (Annotated_V lam_x lam_x_tp)
                                                                                                                                
cpsTransExp (Annotated_F (Tuple (x:xs)) tp) cont                = let  x_tp = fromJust (tCheck x [(" ", Unit)])
                                                                       x1_tp = cpsTransType x_tp
                                                                       lam_x_tp = cpsTransCont tp
                                                                       new_tuple = [(Annotated_V (N_Var "x1") (x1_tp))]
                                                                  in   cpsTransExp (Annotated_F (x) (x_tp)) (Annotated_V (N_Fix ("x_continuation") [] [("x1", x1_tp)] (subList xs new_tuple)) lam_x_tp)
                                                                      where subList xs new_tuple = case xs of 
                                                                                                        [] -> N_App cont [] new_tuple
                                                                                                        (y:ys) -> let y_tp = fromJust (tCheck y [("", Unit)])
                                                                                                                      y_cont = cpsTransCont y_tp
                                                                                                                      y_trans_tp = cpsTransType y_tp
                                                                                                                      new_tuple1 = (Annotated_V (N_Var "x2") (y_trans_tp)) : new_tuple
                                                                                                                  in  cpsTransExp (Annotated_F (y) (y_tp)) (Annotated_V (N_Fix "x_continuation" [] [("x2", (y_trans_tp))] (subList ys new_tuple1)) y_cont)


cpsTransExp (Annotated_F (Proj index e) tp) cont                = let e_tp = fromJust (tCheck e [(" ", Unit)])
                                                                      e_trans_tp = cpsTransType e_tp
                                                                      y_tp = cpsTransType tp
                                                                      lam_x = N_Fix "" [] [("x", e_trans_tp)] (N_Let (Declare_T "y" index (Annotated_V (N_Var "x") (e_trans_tp))) (N_App cont [] [(Annotated_V (N_Var "y") y_tp)]) )
                                                                      lam_x_tp = cpsTransCont tp
                                                                   in cpsTransExp (Annotated_F (Proj index e) (e_tp)) (Annotated_V (lam_x) (lam_x_tp))
cpsTransExp (Annotated_F (PrimOp e1 op e2) tp) cont             = let e1_tp = fromJust (tCheck e1 [(" ", Unit)])
                                                                      e2_tp = fromJust (tCheck e2 [(" ", Unit)])
                                                                  in  case (e1_tp, e2_tp) of
                                                                        (JClass "Int", JClass "Int") -> let lam_x2 = N_Fix "Lam_x2" [] [("x2", N_JClass "Int")] (N_Let (Declare_O "y" (Annotated_V (N_Var "x1") (N_JClass "Int")) op (Annotated_V (N_Var "x2") (N_JClass "Int"))) (N_App cont [] [(Annotated_V (N_Var "y") (N_JClass "Int"))]) )
                                                                                                            lam_x2_cont = cpsTransCont (JClass "Int")
                                                                                                            lam_x1_cont = cpsTransCont (JClass "Int") 
                                                                                                            lam_x1 = N_Fix "Lam_x1" [] [("x1", N_JClass "Int")] (cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont))
                                                                                                        in cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "Bool", JClass "Bool") -> let lam_x2 = N_Fix "Lam_x2" [] [("x2", N_JClass "Bool")] (N_Let (Declare_O "y" (Annotated_V (N_Var "x1") (N_JClass "Bool")) op (Annotated_V (N_Var "x2") (N_JClass "Bool"))) (N_App cont [] [(Annotated_V (N_Var "y") (N_JClass "Bool"))]) )
                                                                                                              lam_x2_cont = cpsTransCont (JClass "Bool")
                                                                                                              lam_x1_cont = cpsTransCont (JClass "Bool") 
                                                                                                              lam_x1 = N_Fix "Lam_x1" [] [("x1", N_JClass "Bool")] (cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont))
                                                                                                          in cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "Char", JClass "Char") -> let lam_x2 = N_Fix "Lam_x2" [] [("x2", N_JClass "Char")] (N_Let (Declare_O "y" (Annotated_V (N_Var "x1") (N_JClass "Char")) op (Annotated_V (N_Var "x2") (N_JClass "Char"))) (N_App cont [] [(Annotated_V (N_Var "y") (N_JClass "Char"))]) )
                                                                                                              lam_x2_cont = cpsTransCont (JClass "Char")
                                                                                                              lam_x1_cont = cpsTransCont (JClass "Char") 
                                                                                                              lam_x1 = N_Fix "Lam_x1" [] [("x1", N_JClass "Char")] (cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont))
                                                                                                          in cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "String", JClass "String") -> let lam_x2 = N_Fix "Lam_x2" [] [("x2", N_JClass "String")] (N_Let (Declare_O "y" (Annotated_V (N_Var "x1") (N_JClass "String")) op (Annotated_V (N_Var "x2") (N_JClass "String"))) (N_App cont [] [(Annotated_V (N_Var "y") (N_JClass "String"))]) )
                                                                                                                  lam_x2_cont = cpsTransCont (JClass "String")
                                                                                                                  lam_x1_cont = cpsTransCont (JClass "String") 
                                                                                                                  lam_x1 = N_Fix "Lam_x1" [] [("x1", N_JClass "String")] (cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont))
                                                                                                              in cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
cpsTransExp (Annotated_F (If e1 e2 e3) tp) cont                   = let e1_tp = fromJust (tCheck e1 [(" ", Unit)])
                                                                        e2_tp = fromJust (tCheck e2 [(" ", Unit)])
                                                                        e3_tp = fromJust (tCheck e3 [(" ", Unit)])
                                                                        x_tp = cpsTransType e1_tp
                                                                        lam_x = N_Fix "lam_x" [] [("x", x_tp)] (N_If (Annotated_V (N_Var "x") x_tp) (cpsTransExp (Annotated_F e2 e2_tp) cont) (cpsTransExp (Annotated_F e3 e3_tp) cont) ) 
                                                                        lam_x_tp = cpsTransCont e1_tp
                                                                    in cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x lam_x_tp)

cpsTransProg :: Annotated_F -> N_Exp
cpsTransProg (Annotated_F e e_tp) = let x_tp = cpsTransType e_tp
                                        intial_cont_tp = cpsTransCont e_tp
                                        initial_contination = N_Fix "initial_contination" [] [("x", x_tp)] (N_Halt (Annotated_V (N_Var "x") x_tp) )
                                    in cpsTransExp (Annotated_F e e_tp) (Annotated_V initial_contination intial_cont_tp)

----------------------------------------CPS Testing--------------------------------------------------
--Annotated_F (Fix name (n, n_tp) e tp) tp_fix
--Fix String (String, Type) Exp Type
--lam x:int. x
main =  let prog = (Fix "Application" ("x", JClass "Int") (Var "x") (JClass "Int"))
            prog_tp = fromJust (tCheck prog [(" ", Unit)])
        in  cpsTransProg (Annotated_F  prog prog_tp)
