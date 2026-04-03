data Access : Type where 
	LoggedIn : Access 
	LoggedOut : Access 


DecEq ((Access)) where 
	decEq (LoggedIn) (LoggedIn) = (Yes Refl)
	decEq (LoggedIn) (LoggedOut) = (No (\(h) => (case (h) of ((Refl)) impossible)))
	decEq (LoggedOut) (LoggedIn) = (No (\(h) => (case (h) of ((Refl)) impossible)))
	decEq (LoggedOut) (LoggedOut) = (Yes Refl)

data LoginResult : Type where 
	OK : LoginResult 
	BadPassword : LoginResult 


DecEq ((LoginResult)) where 
	decEq (OK) (OK) = (Yes Refl)
	decEq (OK) (BadPassword) = (No (\(h) => (case (h) of ((Refl)) impossible)))
	decEq (BadPassword) (OK) = (No (\(h) => (case (h) of ((Refl)) impossible)))
	decEq (BadPassword) (BadPassword) = (Yes Refl)

record Store where 
	constructor MkStore
	secret : String 
	pub : String 


DecEq ((Store)) where 
	decEq (MkStore secret1 pub1) (MkStore secret2 pub2) with (decEq secret1 secret2)
		decEq (MkStore secret1 pub1) (MkStore secret1 pub2) | (Yes Refl)  with (decEq pub1 pub2)
			decEq (MkStore secret1 pub1) (MkStore secret1 pub1) | (Yes Refl) | (Yes Refl)  = (Yes Refl)
			decEq (MkStore secret1 pub1) (MkStore secret1 pub2) | (Yes Refl) | (No prf)  = (No (\(h) => (prf (case (h) of
				((Refl)) => (Refl)))))
		decEq (MkStore secret1 pub1) (MkStore secret2 pub2) | (No prf)  = (No (\(h) => (prf (case (h) of
			((Refl)) => (Refl)))))

data idxmStore : (ty : Type) -> (Access ) -> (ty -> Access ) -> Type where 
	Login : idxmStore LoginResult  (LoggedOut) (\(r) => (case ((decEq r OK)) of
	((Yes yesprf)) => LoggedIn
	((No noprf)) => LoggedOut))
	Logout : idxmStore () (LoggedIn) (\() => (LoggedOut))
	ReadSecret : idxmStore String  (LoggedIn) (\() => (LoggedIn))
	Pure : (x : ty) -> idxmStore ty (st x) st
	(>>=) : (idxmStore a st1 st2) -> ((x : a) -> idxmStore b (st2 x)) -> idxmStore b st1 st3
	Lift : (IO ty) -> idxmStore ty st (const st)


login : IO LoginResult 
(login) = do 
	(putStr "enter password")
	let pw : String  = (getLine)
	if ((pw == "password123")) then (do 
		pure (OK)) else (do 
		pure (BadPassword))

logout : IO ()
(logout) = do 
	(putStr "logging out")
	pure ()

readSecret : IO String 
(readSecret) = do 
	pure st.secret

initStore : (secret : String ) -> (pub : String ) -> Store 
(initStore secret pub) = (Store secret pub)

runidxmStore : (Store ) -> (idxmStore ty  ) -> IO (ty,Store )
(runidxmStore idxmStore (Pure x)) = (pure (x,idxmStore))
(runidxmStore idxmStore (action) >>= (cont)) = ((runidxmStore idxmStore action)) >>= ((\(res, idxmStore) => (runidxmStore idxmStore (cont res))))
(runidxmStore idxmStore (Lift io)) = ((<*>) ((<$>) (,) io) (pure idxmStore))
(runidxmStore idxmStore (Login)) = (login idxmStore)
(runidxmStore idxmStore (Logout)) = (logout idxmStore)
(runidxmStore idxmStore (ReadSecret)) = (readSecret idxmStore)

main : IO ()
(main) = do 
	let st : Store  = (initStore "secret" "pub")
	(res,st) <- (runidxmStore st Login)
	(case ((res == OK)) of
		((Yes yesprf)) => do 
			(secret,st) <- (runidxmStore st ReadSecret)
			(print secret)
			(st) <- (runidxmStore st Logout)
			pure ()
		((No noprf)) => do 
			(print "bad password")
			pure ())