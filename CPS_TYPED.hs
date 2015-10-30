{- |
Module      :  BaseTransCFJava
Description :  Basic translation of FCore to Java
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Unknown
Stability   :  stable
Portability :  non-portable (MPTC)

This module implements the basic translation of FCore to Java. For
more information, please refer to the paper on wiki.
-}


module CPS where

import           Data.Maybe (fromJust)
import qualified Language.Java.Syntax as J (Op(..))

type Name      = String
type ClassName = String

-- Types.
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

------------------------All The Type Checker---------------------------------------------

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
    Char t -> Just (JClass "javachar")
    Int t -> Just (JClass "javaint")
    String t -> Just (JClass "javastring")
    Bool t -> Just (JClass "javabool")
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

