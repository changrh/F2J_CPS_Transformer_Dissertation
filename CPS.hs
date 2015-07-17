{-# Language DeriveDataTypeable,
             FlexibleInstances,
             GeneralizedNewtypeDeriving #-}
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity

import qualified Data.Map as Map

import System.Random

data Expr e = Var e
			      | Lam e (e -> Expr e)
			      | App (Expr e) (Expr e)
            | Lit

instance Show (Expr e) where
  show (Var v) = show "Var " ++ show v
  --show (Lam argument body) = show "Lam " ++ show argument ++ show body
  --show App exp1 exp2 = show "App " ++ show exp1 ++ " " ++ show exp2
  --show Lit = show "Lit"

type Name = String

------------Determine whether an input expression is trivial ----------------------------
isTrivial :: Expr e -> Bool
isTrivial (App _ _) =  True
isTrivial _ = False

------------Define a variable data type to remember the CPSed Unique Variable------------
type VariableID = Int
type VariableName = String
type VarEnv = Map.Map VariableID VariableName

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
genSym :: Compiler (Expr Name)
genSym = do
  i <- gets nextGensymID
  currentVarMap <- gets allGensyms
  modify (\s -> s { nextGensymID = i+1, allGensyms = (Map.insert (i+1) (randomStr (i+1)) currentVarMap) })
  return $ Var (randomStr (i + 1))


