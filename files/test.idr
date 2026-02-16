data idxmStore : (ty : Type) -> (Access ) -> (ty -> Access ) -> Type where 
	Login : idxmStore LoginResult  (LoggedOut) (\(r) => (case ((decEq r OK)) of
	((No noprf)) => LoggedOut
	((Yes yesprf)) => LoggedIn))
	Logout : idxmStore () (LoggedIn) (\() => (LoggedOut))
	ReadSecret : idxmStore String  (LoggedIn) (\() => (LoggedIn))
	Pure : (x : ty) -> idxmStore ty (st x) st
	(>>=) : (idxmStore a st1 st2) -> ((x : a) -> idxmStore b (st2 x)) -> idxmStore b st1 st3
	Lift : (IO ty) -> idxmStore ty st (const st)


login : IO LoginResult 
(login) = do 
	pure 0

logout : IO ()
(logout) = do 
	pure 1

readSecret : IO String 
(readSecret) = do 
	pure st

runidxmStore : (Store ) -> (idxmStore ty  ) -> IO (ty,Store )
(runidxmStore idxmStore (Pure x)) = (pure (x,idxmStore))
(runidxmStore idxmStore (action) >>= (cont)) = ((runidxmStore idxmStore action)) >>= ((\(res, idxmStore) => (runidxmStore idxmStore (cont res))))
(runidxmStore idxmStore (Lift io)) = ((<*>) ((<$>) (,) io) (pure idxmStore))
(runidxmStore idxmStore (Login)) = (login idxmStore)
(runidxmStore idxmStore (Logout)) = (logout idxmStore)
(runidxmStore idxmStore (ReadSecret)) = (readSecret idxmStore)

main : IO ()
(main) = do 
	let secret : String  = secret
let st : Store  = (initStore a b)
(res,st) <- (runidxmStore st Login)
pure if (res == OK) then 
		let secret : String  = (readSecret st) in
			let _ = (print IO secret) in
				let st = (logout st) in
					()
else 
		let _ = (print IO) in
			()



