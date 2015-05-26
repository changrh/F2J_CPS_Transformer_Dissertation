data Expr e = Var e
			| Lam (e -> Expr e)
			| App (Expr e) (Expr e)


trivial? :: Expr e -> Bool
trivial? Var 