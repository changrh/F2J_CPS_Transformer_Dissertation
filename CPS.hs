{-# Language DeriveDataTypeable,
             FlexibleInstances,
             GeneralizedNewtypeDeriving #-}
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity

import qualified Data.Map as Map

import System.Random
---------------------------Note : No pretty print for polymorphic expression -------------
data Expr e = Var e
      | Lam e (e -> Expr e)  -----------------Lam argument body where body is a haskell function waiting for one argument
      | App (Expr e) (Expr e)
      | Lit
--instance Show (Expr e) where
--  show (Var v) = show "Var " ++ show v
--  show (Lam argument body) = show "Lam " ++ show argument ++ show body？？
--  show (App exp1 exp2) = show "App " ++ show exp1 ++ " " ++ show exp2
--  show Lit = show "Lit"

type Name = String

------------Determine whether an input expression is trivial ----------------------------
isTrivial :: Expr e -> Bool
isTrivial (App _ _) =  True
isTrivial _ = False

------------Define a variable data type to remember the CPSed Unique Variable------------
type VariableID = Int
type VariableName = String
type VarEnv = Map.Map VariableID VariableName

type Index = Int

------------Define a state data type to count the unique ID of each variable-------------

data CompilerState = CompilerState { nextGensymID :: VariableID,
                                     allGensyms :: VarEnv }

------------Error data type used to record CPS process error-----------------------------
data CompilerError = XUnboundVariable String
                   | XInternalError String
      deriving (Show)
------------Define a data type to combine every information needed to do CPS-------------
newtype Compiler a = Compiler { runComp :: ErrorT CompilerError (State CompilerState) a }
        deriving (Monad, MonadState CompilerState, MonadError CompilerError)

instance Error CompilerError where
  strMsg = XInternalError

-----------Extract CPSed expression from the wrapped Monad Transformers-----------------
runCompiler :: Compiler a -> Either CompilerError a
runCompiler x = evalState ( runErrorT ( runComp x ) ) state
  where state = CompilerState { nextGensymID = 0, allGensyms = (Map.insert 0 "%root-k" Map.empty) }

----------------------randomStr is used to generate random string-----------------------
randomStr :: Int -> String
randomStr seed = take 6 . randomRs ('a','z') $ (mkStdGen seed)

--Generate fresh variable accoding to the unique ID to make sure every variable is unique---
genSym :: Compiler (Expr Index)
genSym = do
  i <- gets nextGensymID
  currentVarMap <- gets allGensyms
  modify (\s -> s { nextGensymID = i+1, allGensyms = (Map.insert (i+1) (randomStr (i+1)) currentVarMap) })
  return $ Var i--------------?????
---------------------Assign Unique ID to every lexical variable------------------------
giveVariableUniqueIDs :: Expr e -> Compiler (Expr Index)
giveVariableUniqueIDs expression = 
  case expression of 
    Var var -> do
      currentVarMap <- gets allGensyms
      case Map.lookup var currentVarMap of
        Nothing -> 
        Just var' -> 

    Lam argument fbody -> do
      argument' <- genSym argument
      body' <- giveVariableUniqueIDs (body argument)-----problem ??? e -> Expr e , how to CPS this??
      return $ Lam argument' body'

    App exp1 exp2 -> do
      cpsed_exp1 <- giveVariableUniqueIDs exp1
      cpsed_exp2 <- giveVariableUniqueIDs exp2
      return $ App cpsed_exp1 cpsed_exp2
      
    Lit -> return Lit

------------------------Check Validation-----------------
--checkValid :: Expr Name -> Expr Name
--checkValid expression = 
--  case expression of 
--    Var var -> Var "adasdsa"
--    Lam argument body -> Lam "asdas" (\x -> Var "asdasd")