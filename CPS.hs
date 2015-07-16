import Control
data Expr e = Var e
			| Lam e (e -> Expr e)
			| App (Expr e) (Expr e)

--Determine whether an expression is trivial or serious
--trivial? :: Expr e -> Bool
--trivial? Var x = return True
--trivial? Lam _ = return True
--trivial? App e1 e2 = return False

--serious? :: Expr e -> Bool
--serious? Var x = return False
--serious? Lam _ = return False
--serious? App e1 e2 = return True

isCPStrivial? :: Expr e -> Bool
isCPStrivial? App _ _ = return True
isCPStrivial? _ = return False
---------------------------------------------------------

data E v  =  EVariable     v
          |  ELambda 	  v    (E v)
          |  EApplication  (E v)  (E v)

type ES  = E String
type EV  = E Variable

data CompilerState = CompilerState { csNextGensymID :: Integer}
type Compiler a =  StateT CompilerState Identity a

data Variable = MkVariable {  variableID    :: Integer,
                              variableName  :: String }
    deriving (Eq, Data, Typeable, Show)

data CPS  =  CPSVariable        Variable
          |  CPSLambda     Variable    CPS
          |  CPSApplication     CPS         CPS  
    deriving (Eq, Data, Typeable, Show)

--Generate a fresh variable when performing the CPS transformation
gensym :: String -> Expr e
gensym name = do  i <- gets csNextGensymID
                  modify (\s -> s { csNextGensymID = i + 1 })
                  return (MkVariable i name)

(@@) :: CPS -> CPS -> CPS
(@@) = CPSApplication




