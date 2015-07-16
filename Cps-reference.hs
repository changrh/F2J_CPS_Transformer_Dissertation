{-# Language DeriveDataTypeable,
             FlexibleInstances,
             GeneralizedNewtypeDeriving #-}
import Data.Generics


import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity

import qualified Data.Map as Map

data E v = EVariable v
		 | EAbstraction v (E v)
		 | EApplication (E v) (E v)
		 | EPrimitive Integer
		 deriving (Show)


--------------Make E v an instance of Num so that this data type can be used to do numeric operations-------------
instance Num (E v) where
	(+) (EPrimitive x1) (EPrimitive x2) = EPrimitive (x1 + x2)
	(-) (EPrimitive x1) (EPrimitive x2) = EPrimitive (x1 - x2)
	(*) (EPrimitive x1) (EPrimitive x2) = EPrimitive (x1 * x2)
	negate (EPrimitive x) = EPrimitive $ negate x
	abs (EPrimitive x) = EPrimitive $ abs x
	fromInteger x = EPrimitive x 



type ES = E String
type EV = E Variable

--------------------------Variable with Unique ID--------------------------------
data Variable = MkVariable { variableID   :: Integer,
							 variableName :: String }
	deriving (Eq, Data, Typeable, Show)

--------------------------Convert Parsed E v data type to CPS data type----------
data CPS = CPSVariable Variable
		 | CPSAbstraction Variable CPS
		 | CPSApplication CPS CPS
		 | CPSPrimitive Integer
	deriving (Eq, Data, Typeable, Show)


data CompilerState = CompilerState { csNextGensymID :: Integer }

data CompilerError = XUnboundVariable String 
				   | XInternalError String
				   | XInsaneCPS CPS
		deriving (Show)

newtype Compiler a = Compiler {runC :: ErrorT CompilerError (State CompilerState) a}
    deriving (Monad, MonadState CompilerState, MonadError CompilerError)


instance Error CompilerError where
	strMsg = XInternalError

runCompiler :: Compiler a -> Either CompilerError a
runCompiler x = evalState (runErrorT (runC x)) state
	where state = CompilerState { csNextGensymID = 0 }

------------------Add mapping to Map-----------------------------------------------
withBidings :: Ord k => Map.Map k a -> [(k,a)] -> Map.Map k a
withBidings m xs = Map.union (Map.fromList xs) m


--------------------Generate a fresh variable with the given name.------------------

gensym :: String -> Compiler Variable
gensym name = do 
				 i <- gets csNextGensymID 
				 modify (\s -> s {csNextGensymID = i + 1})
				 return (MkVariable i name)

--------------------Assign Unique ID to every lexical variable----------------------
giveVariableUniqueIDs :: ES -> Compiler EV
giveVariableUniqueIDs = f Map.empty
   where 
   	f renamings expression = 
   		case expression of 
   			EVariable var ->
   			    case Map.lookup var renamings of
   			        Nothing -> throwError $ XUnboundVariable var
   			        Just var' -> return $ EVariable var'
   			EAbstraction argument body -> do
   				argument' <- gensym argument
   				body' <- f (renamings `withBidings` (zip (argument:[]) (argument':[]))) body
   				return $ EAbstraction argument' body'
   			EApplication exp1 exp2  -> 
   				liftM2 EApplication (f renamings exp1) (f renamings exp2)
   			EPrimitive n -> 
   				return $ EPrimitive n


isTrivial :: EV -> Compiler Bool
isTrivial (EApplication _ _) =  return False
isTrivial _ = return True


(@@) :: CPS -> CPS -> CPS
(@@) = CPSApplication


---------------------Convert an input expression to Continuation Passing Style--------
convertToCPS :: EV -> Compiler CPS
convertToCPS e = do
	k <- gensym "%root-k"
	isTri <- isTrivial e
	if isTri 
		then do 
			cps <- cpsify-trivial e (CPSVariable k)
	else
		do
			cps <- cpsify-serious e (CPSVariable k)
	return $ CPSAbstraction k $ cps 
---------------------CPS Trivial terms according to the paper--------------------
cpsify-trivial :: EV -> CPS -> Compiler CPS
cpsify-trivial e k = case e of 
						EVariable var -> return (k @@ CPSVariable var)
						EAbstraction argument body -> do
														k1 <- gensym "%new-k"
														isTri <- isTrivial body
														if isTri 
															then do
																cps-body <- cpsify-trivial body k1
														else 
															do
																cps-body <- cpsify-serious body k1
														return (k @@ (CPSAbstraction argument $ CPSAbstraction k1 $ cps-body))  

---------------------CPS Serious Terms according to the paper--------------------
cpsify-serious :: EV -> CPS -> Compiler CPS


