{-# Language DeriveDataTypeable,
             FlexibleInstances,
             GeneralizedNewtypeDeriving #-}
import Data.Generics


import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity

import System.Random

import qualified Data.Map as Map

data E v = EVariable v
		 | EAbstraction v (E v)
		 | EApplication (E v) (E v)
		 | EPrimitive Int
		 deriving (Show)


--------------Make E v an instance of Num so that this data type can be used to do numeric operations-------------
instance Num (E v) where
	(+) (EPrimitive x1) (EPrimitive x2) = EPrimitive (x1 + x2)
	(-) (EPrimitive x1) (EPrimitive x2) = EPrimitive (x1 - x2)
	(*) (EPrimitive x1) (EPrimitive x2) = EPrimitive (x1 * x2)
	negate (EPrimitive x) = EPrimitive $ negate x
	abs (EPrimitive x) = EPrimitive $ abs x


type ES = E String
type EV = E Variable

--------------------------Variable with Unique ID--------------------------------
data Variable = MkVariable { variableID   :: Int,
							 variableName :: String }
	deriving (Eq, Data, Typeable, Show)

--------------------------Convert Parsed E v data type to CPS data type----------
data CPS = CPSVariable Variable
		 | CPSAbstraction Variable CPS
		 | CPSApplication CPS CPS
		 | CPSPrimitive Int
	deriving (Eq, Data, Typeable, Show)


data CompilerState = CompilerState { csNextGensymID :: Int }

data CompilerError = XUnboundVariable String 
				   | XInternalError String
				   | XInsaneCPS CPS
		deriving (Show)

type Compiler a = ErrorT CompilerError (State CompilerState) a

--instance (Error e, MonadIO m) => MonadIO (ErrorT e m) where
--	liftIO = lift . liftIO


instance Error CompilerError where
	strMsg = XInternalError


----------------------randomStr is used to generate random string-----------------------
randomStr :: Int -> String
randomStr seed = take 6 . randomRs ('a','z') $ (mkStdGen seed)


runCompiler :: Compiler a -> Either CompilerError a
runCompiler x = evalState (runErrorT x) state
	where state = CompilerState { csNextGensymID = 0 }

------------------Add mapping to Map-----------------------------------------------
withBidings :: Ord k => Map.Map k a -> [(k,a)] -> Map.Map k a
withBidings m xs = Map.union (Map.fromList xs) m


--------------------Generate a fresh variable with the given name.------------------

--gensym :: String -> Compiler Variable
--gensym name = do 
--				 i <- gets csNextGensymID 
--				 modify (\s -> s {csNextGensymID = i + 1})
--				 return (MkVariable i name)

gensym :: Compiler Variable
gensym = do 
		 i <- gets csNextGensymID 
		 modify (\s -> s {csNextGensymID = i + 1})
		 return (MkVariable i (randomStr i))

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
   				argument' <- gensym
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
	k <- gensym
	cps <- epsilonE e (CPSVariable k)
	return $ CPSAbstraction k $ cps  

-----------------------Function epsilonE----------------------------------------------
epsilonE :: EV -> CPS -> Compiler CPS 
epsilonE e k = do
	istri <- isTrivial e  
	if istri 
		then do 
			trivial_term <- trivialE e
			return (k @@ trivial_term)
	else do
		computations <- cpsify_serious e k
		return computations
------------------------Function Trivial--------------------------------------------
trivialE :: EV -> Compiler CPS
trivialE e =
	case e of
		EVariable var -> return $ CPSVariable var 
		EAbstraction argument body -> do
			k <- gensym
			cps_body <- epsilonE body $ CPSVariable k
			return $ CPSAbstraction argument $ CPSAbstraction k $ cps_body

-----------------------CPS Serious Terms according to the paper--------------------
cpsify_serious :: EV -> CPS -> Compiler CPS
cpsify_serious e k = 
	case e of 
		EApplication exp1 exp2 -> do
			bool_value1 <- isTrivial exp1
			bool_value2 <- isTrivial exp2 
			case (bool_value1, bool_value2) of
				(True, True) -> do 
					exp1_temp <- trivialE exp1
					exp2_temp <- trivialE exp2
					return ((exp1_temp @@ exp2_temp) @@ k)
				(True, False) -> do
					exp1_temp <- trivialE exp1
					x1 <- gensym
					new_continuation <- return $ CPSAbstraction x1 (exp1_temp @@ CPSVariable x1 @@ k)
					cpsify_serious exp2 $ new_continuation 
				(False, True) -> do
					exp2_temp <- trivialE exp2
					x0 <- gensym 
					new_continuation <- return $ CPSAbstraction x0 (CPSVariable x0 @@ exp2_temp @@ k)
					cpsify_serious exp1 $ new_continuation
				(False, False) -> do
					x0 <- gensym
					x1 <- gensym
					inner_new_continuation <- return $ CPSAbstraction x1 (CPSVariable x0 @@ CPSVariable x1 @@ k)
					cpsed_expr2 <- cpsify_serious exp2 inner_new_continuation
					new_continuation <- return $ CPSAbstraction x0 cpsed_expr2
					cpsify_serious exp1 $ new_continuation	

-----------------------These functions are just used for printing out test cases' results------------------
linkAll :: Compiler EV -> Compiler CPS
linkAll x = do 
	expression <- x
	convertToCPS expression

convertToIO :: Compiler CPS -> IO ()
convertToIO x = print $ runCompiler x

main =
	convertToIO $ linkAll $ giveVariableUniqueIDs $ EApplication (EAbstraction "x" (EAbstraction "y" (EApplication (EVariable "x") (EVariable "y"))))  (EAbstraction "w" (EVariable "w"))
	