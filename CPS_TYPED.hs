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
import Control.Monad.State

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
    _ -> error "Lit Error Occurs!"
tCheck (App e1 e2) tenv           = 
  case (tCheck e1 tenv, tCheck e2 tenv) of
    (Just t1, Just t2) -> case t1 of 
                            Fun inType outType -> if inType == t2 then Just (outType) else Nothing
                            _ -> Nothing
    _ -> error "App Error Occurs!"

tCheck (Lam (n, t) e) tenv      = 
  case tCheck e ((n,t) : tenv) of 
      Just t1 -> Just (Fun t t1)
      _ -> error "Lam Error Occurs!"

tCheck (BLam n e) tenv          = 
  case tCheck e tenv of 
    Just t1 -> Just (Forall n t1)
    _ -> error "BLam Error Occurs!"

tCheck (Let (n, t1) e body) tenv = Just Unit

tCheck (TApp e t) tenv          = Just (substitute (Forall alpha tp) (alpha, t))
  where Forall alpha tp = fromJust (tCheck e tenv)

tCheck (PrimOp e1 op e2) tenv   =
  case (tCheck e1 tenv, tCheck e2 tenv) of
    (Just t1, Just t2) -> tbinary op t1 t2
    (Nothing, _)  -> error "PrimOp Left Error Occurs!"
    (Just t1, Nothing)  -> error "PrimOp Right Error Occurs!"
tCheck (If p e1 e2) tenv        =
  case tCheck p tenv of
    Nothing -> Nothing
    Just (JClass "Bool") -> case tCheck e1 tenv of 
                              Nothing -> error "If Bool Error Occurs!"
                              Just t1 -> if (Just t1 == (tCheck e2 tenv)) then Just t1 else Nothing
    Just (JClass "Int") -> case tCheck e1 tenv of 
                              Nothing -> error "If Int Error Occurs!"
                              Just t1 -> if (Just t1 == (tCheck e2 tenv)) then Just t1 else Nothing
    _ -> error "If Error Occurs!"

tCheck (Proj index e) tenv        = 
  case e of 
    Tuple xs -> tCheck (xs !! index) tenv
    _ -> error "Proj Error Occurs!"


tCheck (Tuple (x:xs)) tenv      =  let out = TupleType (fromJust((tCheck x tenv)):subList xs tenv)
                                       subList xs tenv = case xs of
                                                                [] -> []
                                                                (y:ys) -> fromJust(tCheck y tenv) : (subList ys tenv) 
                                   in 
                                      Just out

tCheck (Fix n1 (n2, t1) e t2) tenv  = case tCheck e ((n2, t1) : (n1, (Fun t1 t2)) : tenv) of
                                        Nothing -> error "Fix Error Occurs!"
                                        Just t -> if (t == t2) then (Just (Fun t1 t2)) else error "Fix Type Does Not Match !!"
                                        
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

------------------------------Incorporate State Monad into CPS data types------------------------------

data Environment = Environment { funcNameID :: Int,
                                 varNameID :: Int,
                                 tCheckEnv :: TEnv,
                                 varEnv :: [(String, N_Type)]
                               }
type CPS_State a = State Environment a



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

cpsTransExp :: Annotated_F -> Annotated_V -> CPS_State N_Exp
cpsTransExp (Annotated_F (Var name) tp) cont                   = let name_tp = cpsTransType tp
                                                                 in  return ( N_App cont [] [(Annotated_V (N_Var name) (name_tp))] ) 
cpsTransExp (Annotated_F (Lit n) tp) cont                      = let lit_tp = cpsTransType tp
                                                                 in  return ( N_App cont [] [(Annotated_V (N_Lit n) (lit_tp))] )
cpsTransExp (Annotated_F (BLam name e) tp) cont                = case tp of 
                                                                    Forall n t -> (let c_tp = cpsTransCont t
                                                                                       exp_tp = cpsTransType tp                                                                                  
                                                                                    in 
                                                                                      do  funcID <- gets funcNameID
                                                                                          varID <- gets varNameID
                                                                                          varEnvironment <- gets varEnv
                                                                                          let functionName = "BLam_" ++ show funcID
                                                                                              varName = "Var_" ++ show varID
                                                                                          modify (\s -> s {varNameID = varID + 1,funcNameID = funcID + 1, varEnv = (varName, c_tp) : varEnvironment})
                                                                                          cps_e <- (cpsTransExp (Annotated_F e t) (Annotated_V (N_Var varName) c_tp) )
                                                                                          let exp = (N_Fix functionName [name] [(varName, c_tp)] cps_e)
                                                                                          return ( N_App cont [] [(Annotated_V exp exp_tp)] ) 
                                                                                  )
cpsTransExp (Annotated_F (App e1 e2) tp) cont                  =  do 
                                                                     tenv <- gets tCheckEnv
                                                                     funcID <- gets funcNameID
                                                                     varEnvironment <- gets varEnv
                                                                     varID <- gets varNameID
                                                                     let e1_tp = fromJust (tCheck e1 tenv)
                                                                         e2_tp = fromJust (tCheck e2 tenv)
                                                                         functionName_1 = "Lam_" ++ show funcID
                                                                         functionName_2 = "Lam_" ++ show (funcID + 1)
                                                                         varName_1 = "Var_" ++ show varID
                                                                         varName_2 = "Var_" ++ show (varID + 1)
                                                                         u1 = Annotated_F e1 e1_tp
                                                                         u2 = Annotated_F e2 e2_tp
                                                                         u1_cont = cpsTransCont e1_tp
                                                                         u2_cont = cpsTransCont e2_tp
                                                                         x1_tp   = cpsTransType e1_tp
                                                                         x2_tp   = cpsTransType e2_tp
                                                                         lam_x2  = N_Fix functionName_2 [] [(varName_2, x2_tp)] (N_App (Annotated_V (N_Var varName_1) x1_tp) [] [(Annotated_V (N_Var varName_2) x2_tp), cont])
                                                                     cps_lam_x2 <- cpsTransExp u2 (Annotated_V lam_x2 u2_cont)
                                                                     --cpsTransExp u2 (Annotated_V lam_x2 u2_cont)
                                                                     let lam_x1  = N_Fix functionName_1 [] [(varName_1, x1_tp)] cps_lam_x2
                                                                     modify (\s -> s {varNameID = varID + 2,funcNameID = funcID + 2, varEnv = (varName_1, x1_tp) : (varName_2, x2_tp) : varEnvironment})
                                                                     cpsTransExp u1 (Annotated_V lam_x1 u1_cont)

cpsTransExp (Annotated_F (Fix name (n, n_tp) e tp) tp_fix) cont = let n_trans_tp  = cpsTransType n_tp
                                                                      c_tp   = cpsTransCont tp
                                                                      fix_tp = cpsTransType tp_fix
                                                                  in 
                                                                      do varID <- gets varNameID
                                                                         varEnvironment <- gets varEnv
                                                                         tenv <- gets tCheckEnv
                                                                         let varName = "Var_" ++ show varID
                                                                             new_tenv = fromJust (tCheck (Fix name (n, n_tp) e tp) tenv) 
                                                                         modify (\s -> s {varNameID = varID + 1, varEnv = (varName, c_tp) : varEnvironment, tCheckEnv = (n, n_tp):(name, new_tenv): tenv })
                                                                         cps_e <- (cpsTransExp (Annotated_F e tp) (Annotated_V (N_Var varName) c_tp))
                                                                         let fix_trans = N_Fix name [] [(n, n_trans_tp),(varName, c_tp)] cps_e
                                                                         return (N_App cont [] [(Annotated_V fix_trans fix_tp)])
cpsTransExp (Annotated_F (TApp e ay_tp) tp) cont                = do
                                                                    tenv <- gets tCheckEnv
                                                                    varID <- gets varNameID
                                                                    funcID <- gets funcNameID
                                                                    varEnvironment <- gets varEnv
                                                                    let e_tp = fromJust (tCheck e tenv)
                                                                        x_tp = cpsTransType e_tp
                                                                        ay_tran_tp = cpsTransType ay_tp
                                                                        functionName = "Lam_" ++ show funcID
                                                                        varName = "Var_" ++ show varID
                                                                        lam_x = N_Fix functionName [] [(varName, x_tp)] (N_App (Annotated_V (N_Var varName) x_tp) [ay_tran_tp] [cont])
                                                                        lam_x_tp = cpsTransCont e_tp 
                                                                    modify (\s -> s {varNameID = varID + 1,funcNameID = funcID + 1, varEnv = (varName, x_tp) : varEnvironment})                                                                                       
                                                                    cpsTransExp (Annotated_F e e_tp) (Annotated_V lam_x lam_x_tp)
                                                                                                                                
cpsTransExp (Annotated_F (Tuple (x:xs)) tp) cont                = do
                                                                    tenv <- gets tCheckEnv
                                                                    varID <- gets varNameID
                                                                    funcID <- gets funcNameID
                                                                    varEnvironment <- gets varEnv
                                                                    let  x_tp = fromJust (tCheck x tenv)
                                                                         x1_tp = cpsTransType x_tp
                                                                         lam_x_tp = cpsTransCont x_tp
                                                                         varName = "Var_" ++ show varID
                                                                         functionName = "Lam_" ++ show funcID
                                                                         new_tuple = [(Annotated_V (N_Var varName) (x1_tp))]
                                                                    modify (\s -> s {varNameID = varID + 1,funcNameID = funcID + 1, varEnv = (varName, x1_tp) : varEnvironment})
                                                                    cps_rest <- (subList xs new_tuple)   
                                                                    cpsTransExp (Annotated_F (x) (x_tp)) (Annotated_V (N_Fix functionName [] [(varName, x1_tp)] cps_rest) lam_x_tp)
                                                                        where subList xs new_tuple = case xs of 
                                                                                                        [] -> return (N_App cont [] new_tuple)
                                                                                                        (y:ys) -> do
                                                                                                                    tenv_1 <- gets tCheckEnv
                                                                                                                    varID_1 <- gets varNameID
                                                                                                                    funcID_1 <- gets funcNameID
                                                                                                                    varEnvironment_1 <- gets varEnv
                                                                                                                    let y_tp = fromJust (tCheck y tenv_1)
                                                                                                                        y_cont = cpsTransCont y_tp
                                                                                                                        y_trans_tp = cpsTransType y_tp
                                                                                                                        varName_1 = "Var_" ++ show varID_1
                                                                                                                        functionName_1 = "Lam_" ++ show funcID_1
                                                                                                                        new_tuple1 = (Annotated_V (N_Var varName_1) (y_trans_tp)) : new_tuple
                                                                                                                    modify (\s -> s {varNameID = varID_1 + 1,funcNameID = funcID_1 + 1, varEnv = (varName_1, y_trans_tp) : varEnvironment_1}) 
                                                                                                                    cps_rest_1 <- (subList ys new_tuple1)
                                                                                                                    cpsTransExp (Annotated_F (y) (y_tp)) (Annotated_V (N_Fix functionName_1 [] [(varName_1, (y_trans_tp))] cps_rest_1) y_cont)


cpsTransExp (Annotated_F (Proj index e) tp) cont                = do
                                                                    tenv <- gets tCheckEnv
                                                                    varID <- gets varNameID
                                                                    funcID <- gets funcNameID
                                                                    varEnvironment <- gets varEnv
                                                                    let e_tp = fromJust (tCheck e tenv)
                                                                        e_trans_tp = cpsTransType e_tp
                                                                        y_tp = cpsTransType tp
                                                                        functionName = "Lam_" ++ show funcID
                                                                        varName = "Var_" ++ show varID
                                                                        varName_Y = "Var_" ++ show (varID + 1)
                                                                        lam_x = N_Fix functionName [] [(varName, e_trans_tp)] (N_Let (Declare_T varName_Y index (Annotated_V (N_Var varName) (e_trans_tp))) (N_App cont [] [(Annotated_V (N_Var varName_Y) y_tp)]) )
                                                                        lam_x_tp = cpsTransCont e_tp
                                                                    modify (\s -> s {varNameID = varID + 2,funcNameID = funcID + 1, varEnv = (varName, e_trans_tp) : varEnvironment})
                                                                    cpsTransExp (Annotated_F (Proj index e) (e_tp)) (Annotated_V (lam_x) (lam_x_tp))
cpsTransExp (Annotated_F (PrimOp e1 op e2) tp) cont             = do
                                                                    tenv <- gets tCheckEnv
                                                                    varID <- gets varNameID
                                                                    funcID <- gets funcNameID
                                                                    varEnvironment <- gets varEnv
                                                                    let e1_tp = fromJust (tCheck e1 tenv)
                                                                        e2_tp = fromJust (tCheck e2 tenv)
                                                                        functionName_1 = "Lam_" ++ show funcID
                                                                        functionName_2 = "Lam_" ++ show (funcID + 1)
                                                                        varName_1 = "Var_" ++ show varID
                                                                        varName_2 = "Var_" ++ show (varID + 1)
                                                                        varName_Y = "Var_" ++ show (varID + 2)
                                                                    case (e1_tp, e2_tp) of
                                                                        (JClass "Int", JClass "Int") -> do
                                                                                                          let lam_x2 = N_Fix functionName_2 [] [(varName_2, N_JClass "Int")] (N_Let (Declare_O varName_Y (Annotated_V (N_Var varName_1) (N_JClass "Int")) op (Annotated_V (N_Var varName_2) (N_JClass "Int"))) (N_App cont [] [(Annotated_V (N_Var varName_Y) (N_JClass "Int"))]) )
                                                                                                              lam_x2_cont = cpsTransCont (JClass "Int")
                                                                                                              lam_x1_cont = cpsTransCont (JClass "Int") 
                                                                                                          cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont)
                                                                                                          let lam_x1 = N_Fix functionName_1 [] [(varName_1, N_JClass "Int")] (cps_rest)
                                                                                                          modify (\s -> s {varNameID = varID + 3,funcNameID = funcID + 2, varEnv = (varName_1, N_JClass "Int") : (varName_2, N_JClass "Int") : (varName_Y, cpsTransType tp) : varEnvironment})
                                                                                                          cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "Bool", JClass "Bool") -> do
                                                                                                            let lam_x2 = N_Fix functionName_2 [] [(varName_2, N_JClass "Bool")] (N_Let (Declare_O varName_Y (Annotated_V (N_Var varName_1) (N_JClass "Bool")) op (Annotated_V (N_Var varName_2) (N_JClass "Bool"))) (N_App cont [] [(Annotated_V (N_Var varName_Y) (N_JClass "Bool"))]) )
                                                                                                                lam_x2_cont = cpsTransCont (JClass "Bool")
                                                                                                                lam_x1_cont = cpsTransCont (JClass "Bool") 
                                                                                                            cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont)
                                                                                                            let lam_x1 = N_Fix functionName_1 [] [(varName_1, N_JClass "Bool")] (cps_rest)
                                                                                                            modify (\s -> s {varNameID = varID + 3,funcNameID = funcID + 2, varEnv = (varName_1, N_JClass "Bool") : (varName_2, N_JClass "Bool") : (varName_Y, cpsTransType tp) : varEnvironment})
                                                                                                            cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "Char", JClass "Char") -> do
                                                                                                            let lam_x2 = N_Fix functionName_2 [] [(varName_2, N_JClass "Char")] (N_Let (Declare_O varName_Y (Annotated_V (N_Var varName_1) (N_JClass "Char")) op (Annotated_V (N_Var varName_2) (N_JClass "Char"))) (N_App cont [] [(Annotated_V (N_Var varName_Y) (N_JClass "Char"))]) )
                                                                                                                lam_x2_cont = cpsTransCont (JClass "Char")
                                                                                                                lam_x1_cont = cpsTransCont (JClass "Char") 
                                                                                                            cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont)
                                                                                                            let lam_x1 = N_Fix functionName_1 [] [(varName_1, N_JClass "Char")] (cps_rest)
                                                                                                            modify (\s -> s {varNameID = varID + 3,funcNameID = funcID + 2, varEnv = (varName_1, N_JClass "Char") : (varName_2, N_JClass "Char") : (varName_Y, cpsTransType tp) : varEnvironment})
                                                                                                            cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "String", JClass "String") -> do
                                                                                                                let lam_x2 = N_Fix functionName_2 [] [(varName_2, N_JClass "String")] (N_Let (Declare_O varName_Y (Annotated_V (N_Var varName_1) (N_JClass "String")) op (Annotated_V (N_Var varName_2) (N_JClass "String"))) (N_App cont [] [(Annotated_V (N_Var varName_Y) (N_JClass "String"))]) )
                                                                                                                    lam_x2_cont = cpsTransCont (JClass "String")
                                                                                                                    lam_x1_cont = cpsTransCont (JClass "String") 
                                                                                                                cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont)
                                                                                                                let lam_x1 = N_Fix functionName_1 [] [(varName_1, N_JClass "String")] (cps_rest)
                                                                                                                modify (\s -> s {varNameID = varID + 3,funcNameID = funcID + 2, varEnv = (varName_1, N_JClass "String") : (varName_2, N_JClass "String") : (varName_Y, cpsTransType tp) : varEnvironment})
                                                                                                                cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
cpsTransExp (Annotated_F (If e1 e2 e3) tp) cont                   = do
                                                                      tenv <- gets tCheckEnv
                                                                      varID <- gets varNameID
                                                                      funcID <- gets funcNameID
                                                                      varEnvironment <- gets varEnv
                                                                      let e1_tp = fromJust (tCheck e1 tenv)
                                                                          e2_tp = fromJust (tCheck e2 tenv)
                                                                          e3_tp = fromJust (tCheck e3 tenv)
                                                                          x_tp = cpsTransType e1_tp
                                                                          functionName = "Lam_" ++ show funcID
                                                                          varName = "Var_" ++ show varID
                                                                      modify (\s -> s {varNameID = varID + 1,funcNameID = funcID + 1, varEnv = (varName, x_tp) : varEnvironment})
                                                                      cps_rest_1 <- cpsTransExp (Annotated_F e2 e2_tp) cont
                                                                      cps_rest_2 <- cpsTransExp (Annotated_F e3 e3_tp) cont
                                                                      let lam_x = N_Fix functionName [] [(varName, x_tp)] (N_If (Annotated_V (N_Var varName) x_tp) (cps_rest_1) (cps_rest_2) ) 
                                                                          lam_x_tp = cpsTransCont e1_tp
                                                                      cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x lam_x_tp)

cpsTransProg :: Annotated_F -> CPS_State N_Exp
cpsTransProg (Annotated_F e e_tp) = do 
                                      tenv <- gets tCheckEnv
                                      varID <- gets varNameID
                                      funcID <- gets funcNameID
                                      varEnvironment <- gets varEnv
                                      let x_tp = cpsTransType e_tp
                                          intial_cont_tp = cpsTransCont e_tp
                                          functionName = "Initial_Contination_" ++ show funcID
                                          varName = "Var_" ++ show varID
                                          initial_contination = N_Fix functionName [] [(varName, x_tp)] (N_Halt (Annotated_V (N_Var varName) x_tp) )
                                      modify (\s -> s {varNameID = varID + 1,funcNameID = funcID + 1, varEnv = (varName, x_tp) : varEnvironment})
                                      cpsTransExp (Annotated_F e e_tp) (Annotated_V initial_contination intial_cont_tp)

runCPS :: CPS_State N_Exp -> N_Exp
runCPS x = evalState x initial_state
            where initial_state = Environment { funcNameID = 0, varNameID = 0, tCheckEnv = [(" ", Unit)], varEnv = [(" ", N_Unit)]}

----------------------------------------CPS Evaluator------------------------------------------------
type Env = [(String, Annotated_V)]
type NTEnv = [(String, N_Type)]

evaluate :: N_Exp -> Env -> NTEnv -> Maybe N_Value

evaluate (N_Let dec body) env tenv = evaluate body newEnv tenv
  where newEnv = case dec of 
                  Declare_V n v -> (n, v):env
                  Declare_T n idx tuple -> (n, (fromJust (eval_tuple idx tuple))):env                  
                  Declare_O n (Annotated_V v1 t1) op (Annotated_V v2 t2) -> (n, (fromJust (eval_op op (eval_value v1 env) (eval_value v2 env)))):env
                 
evaluate (N_If av e1 e2) env tenv = 
    if fromJust (eval_bool av) then evaluate e1 env tenv
                               else evaluate e2 env tenv where

      eval_bool (Annotated_V (N_Var x) t) = 
        case lookup x env of
          Nothing -> error "Lookup Error2!"
          Just av -> eval_bool av

      eval_bool (Annotated_V (N_Lit (Bool bv)) (N_JClass "Bool")) = Just bv

      eval_bool (Annotated_V (N_Lit (Int i)) (N_JClass "Int")) = 
        if i == 0 then Just True else Just False

      eval_bool _ = Nothing

evaluate (N_App av ts avs) env tenv = eval_app av where   

  eval_app (Annotated_V (N_Var n) t) = 
    case lookup n env of
        Nothing -> error (show env++n)
        Just av -> eval_app av 
  eval_app func@(Annotated_V (N_Fix f tns pts body) t) = evaluate body newEnv newTEnv
        where newEnv = (zip (map fst pts) avs) ++ ((f, func):env)
              newTEnv = (zip tns ts) ++ tenv

evaluate (N_Halt (Annotated_V v t)) env tenv = Just (eval_value v env) where

eval_tuple :: Int -> Annotated_V -> Maybe Annotated_V
eval_tuple idx (Annotated_V (N_Tuple xs) (N_TupleType ys)) = Just (Annotated_V (xs!!idx) (ys!!idx))
eval_tuple _ _ = Nothing

eval_value :: N_Value -> Env -> N_Value
eval_value (N_Var x) env =
  case lookup x env of
    Nothing -> error "Lookup Error3!"
    Just (Annotated_V v t) -> eval_value v env
eval_value (N_Lit v) env = N_Lit v
eval_value _ _ = error "Unknow value"

eval_op :: Operator -> N_Value -> N_Value -> Maybe Annotated_V
eval_op (Arith J.Add) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Int (a + b))) (N_JClass "Int"))
eval_op (Arith J.Sub) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Int (a - b))) (N_JClass "Int")) 
eval_op (Arith J.Mult) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Int (a * b))) (N_JClass "Int")) 
--eval_op (Arith J.Div) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Int (a 'div' b))) (N_JClass "Integer")) 
--eval_op (Arith J.Rem) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Int (a % b))) (N_JClass "Integer"))  
eval_op (Compare J.GThan) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Bool (a > b))) (N_JClass "Bool")) 
eval_op (Compare J.Equal) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Bool (a == b))) (N_JClass "Bool"))     
eval_op (Compare J.GThanE) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Bool (a >= b))) (N_JClass "Bool")) 
eval_op (Compare J.LThan) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Bool (a < b))) (N_JClass "Bool")) 
eval_op (Compare J.LThanE) (N_Lit (Int a)) (N_Lit (Int b)) = Just (Annotated_V (N_Lit (Bool (a <= b))) (N_JClass "Bool"))

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
--main = let prog = (Fix "factorial" ("n", JClass "Int") 
--                        (If (PrimOp (Var "n") (Compare J.Equal) (Lit (Int 1)) ) 
--                            (Lit (Int 1))
--                            (PrimOp (Var "n") (Arith J.Mult) (App prog (PrimOp (Var "n") (Arith J.Sub) (Lit (Int 1))) ) ) 
--                        ) 
--                        (JClass "Int")
--                  )
--           runProg = App prog (Lit (Int 6))
--           prog_tp = fromJust (tCheck runProg [(" ", Unit)])
--        in (runCPS $ cpsTransProg (Annotated_F  runProg prog_tp) )
        --in fromJust (tCheck prog [(" ", Unit)])
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
-------------------------------TEST CASE 11 -----------------------------------------------------
--fact = N_Fix 
--        "f"
--        []
--        [("n", (N_JClass "Integer")), ("k", (N_Forall [] [(N_JClass "Integer")] N_Void))]
--        (N_If
--          (Annotated_V (N_Var "n") (N_JClass "Integer"))
--          (N_App
--            (Annotated_V 
--                (N_Var "k")
--                (N_Forall [] [(N_JClass "Integer")] N_Void)
--              ) 
--            []
--            [(Annotated_V (N_Lit (Int 1)) (N_JClass "Integer"))]
--          )
--          (N_Let 
--            (Declare_O "x" (Annotated_V (N_Var "n") (N_JClass "Integer")) (Arith J.Sub) (Annotated_V (N_Lit (Int 1)) (N_JClass "Integer")))
--            (N_App
--              (Annotated_V (N_Var "f") (N_Forall [] [(N_JClass "Integer")] N_Void))
--              []
--              [(Annotated_V (N_Var "x") (N_JClass "Integer")), 
--               (Annotated_V
--                  (N_Fix 
--                    "" 
--                    [] 
--                    [("y", (N_JClass "Integer"))]  
--                    (N_Let
--                      (Declare_O "z" (Annotated_V (N_Var "n") (N_JClass "Integer")) (Arith J.Mult) (Annotated_V (N_Var "y") (N_JClass "Integer")))
--                      (N_App
--                        (Annotated_V 
--                          (N_Var "k")
--                          (N_Forall [] [(N_JClass "Integer")] N_Void)
--                        )  
--                        []
--                        [(Annotated_V (N_Var "z") (N_JClass "Integer"))]
--                      )
--                    )
--                  )
--                  (N_Forall [] [(N_JClass "Integer")] N_Void)
--                )
--              ]
--            )
--          )
--        )

--fp = N_App
--      (Annotated_V
--        fact 
--        (N_Forall [] [(N_JClass "Integer")] N_Void)
--      )
--      []
--      [ (Annotated_V (N_Lit (Int 6)) (N_JClass "Integer")), 
--        (Annotated_V 
--          (N_Fix 
--            "" 
--            [] 
--            [("n", (N_JClass "Integer"))] 
--            (N_Halt (Annotated_V (N_Var "n") (N_JClass "Integer")))
--          ) 
--          (N_Forall [] [(N_JClass "Integer")] N_Void)
--        )
--      ]
-----------------------------TEST CASE 12 -----------------------------------------------------
--f 1 = 1 , f n = f (n-1) 
main = let prog = (Fix "recursive" ("n", JClass "Int") 
                        (If (PrimOp (Var "n") (Compare J.Equal) (Lit (Int 1)) ) 
                            (Lit (Int 1))
                            (App (Var "recursive") (PrimOp (Var "n") (Arith J.Sub) (Lit (Int 1))) ) 
                        ) 
                        (JClass "Int")
                  )
           runProg = App prog (Lit (Int 6))
           prog_tp = fromJust (tCheck prog [(" ", Unit)])
        --in evaluate (runCPS $ cpsTransProg (Annotated_F runProg prog_tp) ) [(" ", Annotated_V (N_Lit (Int 0)) (N_JClass "Int") )] [(" ", N_Unit)]
        --in print prog
        in (runCPS $ cpsTransProg (Annotated_F runProg prog_tp) )