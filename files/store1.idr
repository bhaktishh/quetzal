import Data.IORef 

data Access = LoggedOut | LoggedIn 

data LoginResult = OK | BadPassword 

data Store : (ty : Type) -> Access -> (ty -> Access) -> Type where
  Login : Store LoginResult LoggedOut (\res => case res of
      OK => LoggedIn
      BadPassword => LoggedOut)
  Logout : Store () LoggedIn (const LoggedOut)
  ReadSecret : Store String LoggedIn (const LoggedIn)
  Pure : (x : ty) -> Store ty (st x) st
  Lift : IO ty -> Store ty st (const st)
  (>>=) : Store a st1 st2 -> ((x : a) -> Store b (st2 x) st3) -> Store b st1 st3

record DStore where
    constructor MkDStore
    secret : String 
    pub : String

initStore : DStore 
initStore = MkDStore { secret="secret data :O\n", pub="public data\n" }

login : DStore -> IO (LoginResult, DStore)
login store = do
  putStr "enter password: "
  pw <- getLine
  if pw == "password123"
    then do
      pure (OK, store)
    else do
      pure (BadPassword, store)

logout : DStore -> IO ((), DStore)
logout store = do 
    putStrLn "logging out"
    pure ((), store)

readSecret : DStore -> IO (String, DStore)
readSecret store = pure (store.secret, store)

run : DStore -> Store t st1 st2 -> IO (t, DStore)
run store Login = login store 
run store Logout = logout store 
run store ReadSecret = readSecret store 
run store (Pure x) = pure (x, store)
run store (Lift io) = (,) <$> io <*> pure store
run store (action >>= cont) = do 
    (res, store) <- run store action
    run store (cont res)

main' : Store () LoggedOut (const LoggedOut)
main' = do
    res <- Login
    case res of 
        OK => do 
            secret <- ReadSecret
            _ <- Lift $ putStr secret 
            Logout
        BadPassword => do 
            _ <- Lift $ putStr "bad password"
            Pure () 
            
main : IO t
main = do 
    let this = initStore 
    (t, thisConc) <- run st main'
    pure t
