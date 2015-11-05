{- |
Module      :  CPS.LambdaF
Description :  Basic translation of FCore to Java
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Johnny.Lin
Stability   :  stable
Portability :  non-portable (MPTC)

This module implements the continuation passing style of FCore. For
more information, please refer to the paper on wiki.
-}

module CPS.LambdaF where

import           CPS.LamSrc
import           Data.Maybe (fromJust)
import qualified Language.Java.Syntax as J (Op(..))

data Annotated_F = Annotated_F Exp Type

data Type
  = TVar Name
  | JClass ClassName
  | Unit
  | Fun Type Type
  | Forall Name Type
  | TupleType [Type]
  deriving (Eq, Show, Read)

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
tbinary _ _ _ = error "tbinary Error Occurs!"

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
                            _ -> error ("App Left is Not a Function Type! ----> App " ++ show e1 ++ "  " ++ show e2)
    (Nothing, _) -> error "App Left Error Occurs!"
    (Just t1, Nothing) -> error "App Right Error Occurs!"
    _ -> error "App Error Occurs!"

tCheck (Lam (n, t) e) tenv      = 
  case tCheck e ((n,t) : tenv) of 
      Just t1 -> Just (Fun t t1)
      _ -> error "Lam Error Occurs!"

tCheck (BLam n e) tenv          = 
  case tCheck e tenv of 
    Just t1 -> Just (Forall n t1)
    _ -> error "BLam Error Occurs!"

tCheck (Let (n, t1) e body) tenv = case tCheck body ((n,t1):tenv) of
                                        Nothing -> error "Error Occurs in Let type Checker !"
                                        Just t1 -> Just t1

tCheck (TApp e t) tenv          = Just (substitute (Forall alpha tp) (alpha, t))
  where Forall alpha tp = fromJust (tCheck e tenv)

tCheck (PrimOp e1 op e2) tenv   =
  case (tCheck e1 tenv, tCheck e2 tenv) of
    (Just t1, Just t2) -> tbinary op t1 t2
    (Nothing, _)  -> error "PrimOp Left Error Occurs!"
    (Just t1, Nothing)  -> error "PrimOp Right Error Occurs!"
tCheck (If p e1 e2) tenv        =
  case tCheck p tenv of
    Nothing -> error ("If Error occurs " ++ show p)
    Just (JClass "Bool") -> case tCheck e1 tenv of 
                              Nothing -> error "If Bool Error Occurs!"
                              Just t1 -> if (Just t1 == (tCheck e2 tenv)) then (Just t1) else (error "Error occured Bool") 
    Just (JClass "Int") -> case tCheck e1 tenv of 
                              Nothing -> error "If Int Error Occurs!"
                              Just t1 -> if (Just t1 == (tCheck e2 tenv)) then (Just t1) else (error "Error occured Int")
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
                                        Nothing -> error ("Fix Error Occurs!" ++ show ((n2, t1) : (n1, (Fun t1 t2)) : tenv))
                                        Just t -> if (t == t2) then Just (Fun t1 t2) else error "Fix Type Does Not Match !!"
                                        