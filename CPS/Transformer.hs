{- |
Module      :  CPS.Transformer
Description :  Basic translation of FCore to Java
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Johnny.Lin
Stability   :  stable
Portability :  non-portable (MPTC)

This module implements the continuation passing style of FCore. For
more information, please refer to the paper on wiki.
-}


module CPS.Transformer where

import           Data.Maybe (fromJust)
import Control.Monad.State
import qualified Core as C
import qualified Src as S
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           CPS.LambdaF
import           CPS.LambdaK

------------------------------CPS Transformation from SystemF to CPSK----------------------------------

data Environment = Environment { funcNameID :: Int,
                                 varNameID :: Int,
                                 tCheckEnv :: TEnv,
                                 varEnv :: [(String, N_Type)]
                               }

type CPS_State a = State Environment a

cpsTransType :: Type -> N_Type
cpsTransType (TVar name)           = N_TVar name
cpsTransType (JClass name)         = N_JClass name
cpsTransType  Unit                 = N_Unit
cpsTransType (Fun t1 t2)           = N_Forall [] [cpsTransType(t1), cpsTransCont(t2)] N_Void 
cpsTransType (Forall name tp)      = N_Forall [name] [(cpsTransCont tp)] N_Void
cpsTransType (TupleType (x:xs))    = N_TupleType ((cpsTransType x) : subList xs)
                                        where subList xs = case xs of 
                                                                [] -> []
                                                                (y:ys) -> (cpsTransType y) : (subList ys)
cpsTransType (TupleType [])        = error ("TupleType is empty !!!")


cpsTransCont :: Type -> N_Type
cpsTransCont tp = N_Forall [] [(cpsTransType tp)] N_Void

cpsTransExp :: Annotated_F -> Annotated_V -> CPS_State N_Exp
cpsTransExp (Annotated_F (Var name) tp) cont                   = return ( N_App cont [] [(Annotated_V (N_Var name) (cpsTransType tp))] ) 
cpsTransExp (Annotated_F (Lit n) tp) cont                      = return ( N_App cont [] [(Annotated_V (N_Lit n) (cpsTransType tp))] )
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
                                                                    others -> error ("The Type of BLam should be Forall !! Please Check -->" ++ show tp)

cpsTransExp (Annotated_F (App e1 e2) tp) cont                  =  case (isSerious e1, isSerious e2) of 
                                                                        (True, True) -> do 
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
                                                                                         modify (\s -> s {varNameID = varID + 2,funcNameID = funcID + 2, varEnv = (varName_1, x1_tp) : (varName_2, x2_tp) : varEnvironment})
                                                                                         cps_lam_x2 <- cpsTransExp u2 (Annotated_V lam_x2 u2_cont)
                                                                                         --cpsTransExp u2 (Annotated_V lam_x2 u2_cont)
                                                                                         let lam_x1  = N_Fix functionName_1 [] [(varName_1, x1_tp)] cps_lam_x2
                                                                                         cpsTransExp u1 (Annotated_V lam_x1 u1_cont)

                                                                        (True, False) -> do 
                                                                                             tenv <- gets tCheckEnv
                                                                                             funcID <- gets funcNameID
                                                                                             varEnvironment <- gets varEnv
                                                                                             varID <- gets varNameID
                                                                                             let e1_tp = fromJust (tCheck e1 tenv)
                                                                                                 e2_tp = fromJust (tCheck e2 tenv)
                                                                                                 u1 = Annotated_F e1 e1_tp
                                                                                                 u2 = Annotated_F e2 e2_tp
                                                                                                 x_tp = cpsTransType e1_tp
                                                                                                 u1_cont = cpsTransCont e1_tp
                                                                                                 functionName = "Lam_" ++ show funcID
                                                                                                 varName = "Var_" ++ show varID
                                                                                             modify (\s -> s {varNameID = varID + 1,funcNameID = funcID + 1, varEnv = (varName, x_tp) : varEnvironment})
                                                                                             t1 <- cpsTransTrivial u2 
                                                                                             let lam_x = N_Fix functionName [] [(varName, x_tp)] (N_App (Annotated_V (N_Var varName) x_tp) [] [t1, cont]) 
                                                                                             cpsTransExp u1 (Annotated_V lam_x u1_cont)

                                                                        (False, True) -> do 
                                                                                             tenv <- gets tCheckEnv
                                                                                             funcID <- gets funcNameID
                                                                                             varEnvironment <- gets varEnv
                                                                                             varID <- gets varNameID
                                                                                             let e1_tp = fromJust (tCheck e1 tenv)
                                                                                                 e2_tp = fromJust (tCheck e2 tenv)
                                                                                                 u1 = Annotated_F e1 e1_tp
                                                                                                 u2 = Annotated_F e2 e2_tp
                                                                                                 x_tp = cpsTransType e2_tp
                                                                                                 u2_cont = cpsTransCont e2_tp
                                                                                                 functionName = "Lam_" ++ show funcID
                                                                                                 varName = "Var_" ++ show varID
                                                                                             modify (\s -> s {varNameID = varID + 1,funcNameID = funcID + 1, varEnv = (varName, x_tp) : varEnvironment})
                                                                                             t0 <- cpsTransTrivial u1 
                                                                                             let lam_x = N_Fix functionName [] [(varName, x_tp)] (N_App t0 [] [(Annotated_V (N_Var varName) x_tp), cont]) 
                                                                                             cpsTransExp u2 (Annotated_V lam_x u2_cont)

                                                                        (False, False) ->  do 
                                                                                             tenv <- gets tCheckEnv
                                                                                             funcID <- gets funcNameID
                                                                                             varEnvironment <- gets varEnv
                                                                                             varID <- gets varNameID
                                                                                             let e1_tp = fromJust (tCheck e1 tenv)
                                                                                                 e2_tp = fromJust (tCheck e2 tenv)
                                                                                                 u1 = Annotated_F e1 e1_tp
                                                                                                 u2 = Annotated_F e2 e2_tp
                                                                                             t0 <- cpsTransTrivial u1
                                                                                             t1 <- cpsTransTrivial u2
                                                                                             return (N_App t0 [] [t1,cont])

--cpsTransExp (Annotated_F (App e1 e2) tp) cont                  =  do 
--                                                                     tenv <- gets tCheckEnv
--                                                                     funcID <- gets funcNameID
--                                                                     varEnvironment <- gets varEnv
--                                                                     varID <- gets varNameID
--                                                                     let e1_tp = fromJust (tCheck e1 tenv)
--                                                                         e2_tp = fromJust (tCheck e2 tenv)
--                                                                         functionName_1 = "Lam_" ++ show funcID
--                                                                         functionName_2 = "Lam_" ++ show (funcID + 1)
--                                                                         varName_1 = "Var_" ++ show varID
--                                                                         varName_2 = "Var_" ++ show (varID + 1)
--                                                                         u1 = Annotated_F e1 e1_tp
--                                                                         u2 = Annotated_F e2 e2_tp
--                                                                         u1_cont = cpsTransCont e1_tp
--                                                                         u2_cont = cpsTransCont e2_tp
--                                                                         x1_tp   = cpsTransType e1_tp
--                                                                         x2_tp   = cpsTransType e2_tp
--                                                                         lam_x2  = N_Fix functionName_2 [] [(varName_2, x2_tp)] (N_App (Annotated_V (N_Var varName_1) x1_tp) [] [(Annotated_V (N_Var varName_2) x2_tp), cont])
--                                                                     modify (\s -> s {varNameID = varID + 2,funcNameID = funcID + 2, varEnv = (varName_1, x1_tp) : (varName_2, x2_tp) : varEnvironment})
--                                                                     cps_lam_x2 <- cpsTransExp u2 (Annotated_V lam_x2 u2_cont)
--                                                                     --cpsTransExp u2 (Annotated_V lam_x2 u2_cont)
--                                                                     let lam_x1  = N_Fix functionName_1 [] [(varName_1, x1_tp)] cps_lam_x2
--                                                                     cpsTransExp u1 (Annotated_V lam_x1 u1_cont)

cpsTransExp (Annotated_F (Fix name (n, n_tp) e tp) tp_fix) cont = do 
                                                                     varID <- gets varNameID
                                                                     varEnvironment <- gets varEnv
                                                                     tenv <- gets tCheckEnv
                                                                     let n_trans_tp  = cpsTransType n_tp
                                                                         c_tp   = cpsTransCont tp
                                                                         fix_tp = cpsTransType tp_fix
                                                                         varName = "Var_" ++ show varID
                                                                         new_tenv = (n, n_tp):(name, tp_fix): tenv
                                                                     modify (\s -> s {varNameID = varID + 1, varEnv = (varName, c_tp) : varEnvironment, tCheckEnv = new_tenv })
                                                                     let e_tp = fromJust (tCheck e new_tenv)
                                                                     cps_e <- (cpsTransExp (Annotated_F e e_tp) (Annotated_V (N_Var varName) c_tp))
                                                                     let fix_trans =   N_Fix name [] [(n, n_trans_tp),(varName, c_tp)] cps_e
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
                                                                        (JClass "java.lang.Integer", JClass "java.lang.Integer") -> do
                                                                                                                                      modify (\s -> s {varNameID = varID + 3,funcNameID = funcID + 2, varEnv = (varName_1, N_JClass "java.lang.Integer") : (varName_2, N_JClass "java.lang.Integer") : (varName_Y, cpsTransType tp) : varEnvironment}) 
                                                                                                                                      let lam_x2_body = (N_Let (Declare_O varName_Y (Annotated_V (N_Var varName_1) (cpsTransType e1_tp)) op (Annotated_V (N_Var varName_2) (cpsTransType e2_tp))) (N_App cont [] [(Annotated_V (N_Var varName_Y) (cpsTransType tp))]) )
                                                                                                                                          lam_x2 = N_Fix functionName_2 [] [(varName_2, cpsTransType e2_tp)] lam_x2_body
                                                                                                                                          lam_x2_cont = cpsTransCont e2_tp
                                                                                                                                          lam_x1_cont = cpsTransCont e1_tp
                                                                                                                                      cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont)
                                                                                                                                      --let lam_x1 = trace ("cps_rest: " ++ show cps_rest) $ N_Fix functionName_1 [] [(varName_1, cpsTransType e1_tp)] cps_rest
                                                                                                                                      let lam_x1 =  N_Fix functionName_1 [] [(varName_1, cpsTransType e1_tp)] cps_rest
                                                                                                                                      cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "java.lang.Boolean", JClass "java.lang.Boolean") -> do
                                                                                                                                      modify (\s -> s {varNameID = varID + 3,funcNameID = funcID + 2, varEnv = (varName_1, N_JClass "java.lang.Boolean") : (varName_2, N_JClass "java.lang.Boolean") : (varName_Y, cpsTransType tp) : varEnvironment}) 
                                                                                                                                      let lam_x2_body = (N_Let (Declare_O varName_Y (Annotated_V (N_Var varName_1) (cpsTransType e1_tp)) op (Annotated_V (N_Var varName_2) (cpsTransType e2_tp))) (N_App cont [] [(Annotated_V (N_Var varName_Y) (cpsTransType tp))]) )
                                                                                                                                          lam_x2 = N_Fix functionName_2 [] [(varName_2, cpsTransType e2_tp)] lam_x2_body
                                                                                                                                          lam_x2_cont = cpsTransCont e2_tp
                                                                                                                                          lam_x1_cont = cpsTransCont e1_tp
                                                                                                                                      cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont)
                                                                                                                                      --let lam_x1 = trace ("cps_rest: " ++ show cps_rest) $ N_Fix functionName_1 [] [(varName_1, cpsTransType e1_tp)] cps_rest
                                                                                                                                      let lam_x1 =  N_Fix functionName_1 [] [(varName_1, cpsTransType e1_tp)] cps_rest
                                                                                                                                      cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "java.lang.Character", JClass "java.lang.Character") -> do
                                                                                                                                          modify (\s -> s {varNameID = varID + 3,funcNameID = funcID + 2, varEnv = (varName_1, N_JClass "java.lang.Character") : (varName_2, N_JClass "java.lang.Character") : (varName_Y, cpsTransType tp) : varEnvironment}) 
                                                                                                                                          let lam_x2_body = (N_Let (Declare_O varName_Y (Annotated_V (N_Var varName_1) (cpsTransType e1_tp)) op (Annotated_V (N_Var varName_2) (cpsTransType e2_tp))) (N_App cont [] [(Annotated_V (N_Var varName_Y) (cpsTransType tp))]) )
                                                                                                                                              lam_x2 = N_Fix functionName_2 [] [(varName_2, cpsTransType e2_tp)] lam_x2_body
                                                                                                                                              lam_x2_cont = cpsTransCont e2_tp
                                                                                                                                              lam_x1_cont = cpsTransCont e1_tp
                                                                                                                                          cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont)
                                                                                                                                          --let lam_x1 = trace ("cps_rest: " ++ show cps_rest) $ N_Fix functionName_1 [] [(varName_1, cpsTransType e1_tp)] cps_rest
                                                                                                                                          let lam_x1 =  N_Fix functionName_1 [] [(varName_1, cpsTransType e1_tp)] cps_rest
                                                                                                                                          cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (JClass "java.lang.String", JClass "java.lang.String") -> do
                                                                                                                                    modify (\s -> s {varNameID = varID + 3,funcNameID = funcID + 2, varEnv = (varName_1, N_JClass "java.lang.String") : (varName_2, N_JClass "java.lang.String") : (varName_Y, cpsTransType tp) : varEnvironment}) 
                                                                                                                                    let lam_x2_body = (N_Let (Declare_O varName_Y (Annotated_V (N_Var varName_1) (cpsTransType e1_tp)) op (Annotated_V (N_Var varName_2) (cpsTransType e2_tp))) (N_App cont [] [(Annotated_V (N_Var varName_Y) (cpsTransType tp))]) )
                                                                                                                                        lam_x2 = N_Fix functionName_2 [] [(varName_2, cpsTransType e2_tp)] lam_x2_body
                                                                                                                                        lam_x2_cont = cpsTransCont e2_tp
                                                                                                                                        lam_x1_cont = cpsTransCont e1_tp
                                                                                                                                    cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) (Annotated_V lam_x2 lam_x2_cont)
                                                                                                                                    --let lam_x1 = trace ("cps_rest: " ++ show cps_rest) $ N_Fix functionName_1 [] [(varName_1, cpsTransType e1_tp)] cps_rest
                                                                                                                                    let lam_x1 =  N_Fix functionName_1 [] [(varName_1, cpsTransType e1_tp)] cps_rest
                                                                                                                                    cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x1 lam_x1_cont)
                                                                        (_, _) -> error ("Current Operation in PrimOP is not supported !!! ----> " ++ show op)
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


cpsTransExp (Annotated_F (Let (name, tp_name) e1 e2) tp) cont      = do 
                                                                        tenv <- gets tCheckEnv
                                                                        varID <- gets varNameID
                                                                        funcID <- gets funcNameID
                                                                        varEnvironment <- gets varEnv
                                                                        let new_tenv = (name, tp_name):tenv
                                                                            e1_tp = fromJust (tCheck e1 new_tenv)
                                                                            e2_tp = fromJust (tCheck e2 new_tenv)
                                                                            functionName = "Lam_" ++ show funcID
                                                                            varName = "Var_" ++ show varID
                                                                            x_tp = cpsTransType e1_tp
                                                                        modify (\s -> s {varNameID = varID + 1,funcNameID = funcID + 1, varEnv = (varName, x_tp) : varEnvironment, tCheckEnv =  new_tenv})
                                                                        cps_rest <- cpsTransExp (Annotated_F e2 e2_tp) cont
                                                                        let lam_x_body = N_Let (Declare_V name (Annotated_V (N_Var varName) (x_tp))) cps_rest
                                                                            lam_x = N_Fix functionName [] [(varName, x_tp)] lam_x_body
                                                                            lam_x_cont = cpsTransCont tp
                                                                        cpsTransExp (Annotated_F e1 e1_tp) (Annotated_V lam_x lam_x_cont)

cpsTransExp (Annotated_F v v_tp) cont = error ("The expression should not be CPSed, Please Check ----> " ++ show v)


isSerious :: Exp -> Bool
isSerious (Fix name (n, n_tp) e tp) = False
isSerious (Var name) = False
isSerious (Lit n) = False
isSerious others = True

cpsTransTrivial :: Annotated_F -> CPS_State Annotated_V
cpsTransTrivial (Annotated_F (Var name) tp) = return (Annotated_V (N_Var name) (cpsTransType tp))
cpsTransTrivial (Annotated_F (Lit name) tp) = return (Annotated_V (N_Lit name) (cpsTransType tp))
cpsTransTrivial (Annotated_F (Fix name (n, n_tp) e tp) tp_fix) = do 
                                                                     varID <- gets varNameID
                                                                     varEnvironment <- gets varEnv
                                                                     tenv <- gets tCheckEnv
                                                                     let n_trans_tp  = cpsTransType n_tp
                                                                         c_tp   = cpsTransCont tp
                                                                         fix_tp = cpsTransType tp_fix
                                                                         varName = "Var_" ++ show varID
                                                                         new_tenv = (n, n_tp):(name, tp_fix): tenv
                                                                     modify (\s -> s {varNameID = varID + 1, varEnv = (varName, c_tp) : varEnvironment, tCheckEnv = new_tenv })
                                                                     let e_tp = fromJust (tCheck e new_tenv)
                                                                     cps_e <- (cpsTransExp (Annotated_F e e_tp) (Annotated_V (N_Var varName) c_tp))
                                                                     let fix_trans =   N_Fix name [] [(n, n_trans_tp),(varName, c_tp)] cps_e
                                                                     return  (Annotated_V fix_trans fix_tp)    

cpsTransTrivial (Annotated_F v v_tp) = error ("The expression should not be considered a trivial term !!! --->" ++ show v)                                                     

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

----------------------------Convert CPS back to Core------------------------------------------------------------------------------

type TVarMap t  = Map.Map String t
type VarMap t e = Map.Map String (C.Expr t e)

convertType :: TVarMap t -> N_Type -> C.Type t
convertType d (N_TVar name) = C.TVar name (fromMaybe (error ("Error Occur when converting N_TVar " ++ name)) (Map.lookup name d) )
convertType _ (N_JClass name) = C.JClass name
convertType _ (N_Void) = C.Unit
convertType _ (N_Unit) = C.Unit
convertType d (N_TupleType xs) = C.Product (map (convertType d) xs)
convertType d (N_Forall ns tps void) = if (length ns) == 0 then subCvrtFun tps else subCvrtForall ns 
                                         where subCvrtFun tps = case tps of 
                                                                    [] ->  convertType d void
                                                                    (t:ts) -> C.Fun (convertType d t) (subCvrtFun ts) 
                                               subCvrtForall ns = case ns of
                                                                      [] -> convertType d (N_Forall [] tps void)
                                                                      (n:ns') -> C.Forall n (\n' -> convertType (Map.insert n n' d) (N_Forall ns' tps void)) 

convertNValue :: (TVarMap t, VarMap t e) -> Annotated_V -> C.Expr t e
convertNValue (d, g) = go
  where 
    go (Annotated_V (N_Var name) tp) = fromMaybe (error ("Error Occur when converting N_Var " ++ show name)) (Map.lookup name g)
    go (Annotated_V (N_Lit lit) tp)  = C.Lit lit
    go (Annotated_V (N_Fix name tps ((v,v_tp):avs) exp) tp) =  if (length tps) == 0 then (C.Fix name v (\f n -> (let newMap = Map.insert name (C.Var name f) g
                                                                                                                     newMap' = Map.insert v (C.Var v n) newMap
                                                                                                                  in (subCvrtFix avs (d,newMap')) )) (convertType d v_tp) (convertType d (getOutType tp)))  else subCvrtBLam tps (d, g) where 
                             subCvrtFix avs (d, newMap') = case avs of
                                                            [] -> convertNExp (d,newMap') exp
                                                            --(n, t):ys -> C.Lam n (convertType d t) (\x -> subCvrtLam ys (d, Map.insert n (C.Var n x) g)) 
                                                            (n',t):ys -> C.Lam n' (convertType d t) (\x -> subCvrtFix ys (d, Map.insert n' (C.Var n' x) newMap'))
                             subCvrtBLam tps (d, g) = case tps of
                                                            [] -> subCvrtFix avs (d,g)
                                                            (y:ys) -> C.BLam y (\x -> subCvrtBLam ys (Map.insert y x d, g))
                             getOutType tp = case tp of 
                                              (N_Forall args tps void) -> let (_, out) = splitAt 1 tps
                                                                            in (N_Forall args out void)
                                              others -> error ("N_Fix type must be Forall !!! ----> " ++ show others)
    go (Annotated_V (N_Tuple es) tp) = C.Tuple (map go es)
    go (Annotated_V (N_Fix name tps [] exp) tp) = error ("Nothing in N_Fix parameters !!! ---> " ++ show name ) 


convertNExp :: (TVarMap t, VarMap t e) -> N_Exp -> C.Expr t e
convertNExp (d, g) = go
  where
    go (N_Let declare exp) = case declare of
                                  (Declare_V name av) -> let exp1 = (convertNValue (d,g) av)
                                                         in C.Let name exp1 (\x -> convertNExp (d, Map.insert name (C.Var name x) g) exp)
                                  (Declare_O name av1 op av2) -> let exp1 = (convertNValue (d,g) av1)
                                                                     exp2 = (convertNValue (d,g) av2)
                                                                     exp_pass = C.PrimOp exp1 op exp2 
                                                                  in C.Let name exp_pass (\x -> convertNExp (d, Map.insert name (C.Var name x) g) exp)
                                  (Declare_T name index av) -> let exp1 = (convertNValue (d,g) av)
                                                                   exp_pass = C.Proj index exp1
                                                               in C.Let name exp_pass (\x -> convertNExp (d, Map.insert name (C.Var name x) g) exp)

    go (N_If av e1 e2) = let exp1 = (convertNValue (d,g) av)
                          in C.If exp1 (go e1) (go e2) 
    go (N_App av tps avs) = let app_left = (convertNValue (d,g) av)
                            in 
                                if (length tps) == 0 then subCvrtApp app_left avs else subCvrtTApp app_left tps
                                    where subCvrtApp app_left avs = case avs of 
                                                                        [] ->  app_left
                                                                        (y:ys) -> let tmp = (convertNValue (d,g) y)
                                                                                  in subCvrtApp (C.App app_left tmp) ys
                                          subCvrtTApp app_left tps = case tps of 
                                                                          [] -> subCvrtApp app_left avs
                                                                          (y:ys) -> let tmp = convertType d y
                                                                                    in subCvrtTApp (C.TApp app_left tmp) ys 
    go (N_Halt av) = C.Lit (S.UnitLit)