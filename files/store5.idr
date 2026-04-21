import Decidable.Equality

data Access : Type where 
	LoggedIn : Access
	LoggedOut : Access


DecEq Access where 
	decEq LoggedIn LoggedIn = Yes Refl
	decEq LoggedIn LoggedOut = No (\h => case h of Refl impossible)
	decEq LoggedOut LoggedIn = No (\h => case h of Refl impossible)
	decEq LoggedOut LoggedOut = Yes Refl

data LoginResult : Type where 
	OK : LoginResult
	BadPassword : LoginResult


DecEq LoginResult where 
	decEq OK OK = Yes Refl
	decEq OK BadPassword = No (\h => case h of Refl impossible)
	decEq BadPassword OK = No (\h => case h of Refl impossible)
	decEq BadPassword BadPassword = Yes Refl

record Store where 
	constructor MkStore
	secret : String
	pub : String


DecEq Store where 
	decEq (MkStore secret1 pub1) (MkStore secret2 pub2) with (decEq secret1 secret2)
		decEq (MkStore secret1 pub1) (MkStore secret1 pub2) | Yes Refl  with (decEq pub1 pub2)
			decEq (MkStore secret1 pub1) (MkStore secret1 pub1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MkStore secret1 pub1) (MkStore secret1 pub2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (MkStore secret1 pub1) (MkStore secret2 pub2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

login : (this : Store) -> IO (LoginResult, Store)
login this = do 
	_ <- print "enter password"
	pw <- getLine
	if pw == "password123" then
		do 
			pure (OK, this) else
		do 
			pure (BadPassword, this)

logout : (this : Store) -> IO ((), Store)
logout this = do 
	_ <- print "logging out"
	pure ((), this)

readSecret : (this : Store) -> IO (String, Store)
readSecret this = do 
	pure (this.secret, this)

mkStore : (secret : String) -> (pub : String) -> Store
mkStore secret pub = MkStore secret pub

main : IO ()
main = do 
	let this = mkStore "secret" "pub"
	(resVal,resConc) <- runStore_Access this main'
	pure resVal
where 
	main' : IdxmStore_Access () LoggedOut (const LoggedOut)
	main' = do 
		res <- Login
		case decEq res OK of
			Yes yesprf => do 
				secret <- ReadSecret
				_ <- LiftStore_Access (print secret)
				_ <- Logout
				PureStore_Access ()
			No noprf => do 
				_ <- LiftStore_Access (print "bad password")
				PureStore_Access ()

data IdxmStore_Access : (ty : Type) -> (Access) -> (ty -> Access) -> Type where 
	Login : IdxmStore_Access LoginResult LoggedOut (\r => case decEq r OK of
		Yes yesprf => LoggedIn
		No noprf => LoggedOut)
	Logout : IdxmStore_Access () LoggedIn (const LoggedOut)
	ReadSecret : IdxmStore_Access String LoggedIn (const LoggedIn)
	PureStore_Access : (x : ty) -> IdxmStore_Access ty (st x) st
	(>>=) : (IdxmStore_Access a st1 st2) -> ((x : a) -> IdxmStore_Access b (st2 x) st3) -> IdxmStore_Access b st1 st3
	LiftStore_Access : (IO ty) -> IdxmStore_Access ty st (const st)


runStore_Access : (Store) -> (IdxmStore_Access ty var2 var3) -> IO (ty, Store)
runStore_Access resource (PureStore_Access x) = pure (x, resource)
runStore_Access resource (action >>= cont) = do 
	(res,resource) <- runStore_Access resource action
	runStore_Access resource (cont res)
runStore_Access resource (LiftStore_Access io) = map (\t => (t, resource)) io
runStore_Access resource Login = login resource
runStore_Access resource Logout = logout resource
runStore_Access resource ReadSecret = readSecret resource



