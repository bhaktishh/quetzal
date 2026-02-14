module ST2

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

initDStore : (String, String) -> DStore 
initDStore (secret, pub) = MkDStore secret pub  

login : DStore -> IO (LoginResult, DStore)
login store = do
  putStr "Enter password: "
  password <- getLine
  if password == "secret123"
    then do
      putStrLn "Login successful!"
      pure (OK, store)
    else do
      putStrLn "Login failed!"
      pure (BadPassword, store)

logout : DStore -> IO ((), DStore)
logout store = do 
    putStrLn "Logged out"
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

-- Main program
main : IO ()
main = do
    let store = initDStore("secret", "pub")
    (res, store) <- run store Login
    case res of 
        OK => do 
            (secret, store) <- run store ReadSecret
            putStr ("Secret: " ++ show secret ++ "\n")
            _ <- run store Logout
            pure ()
        BadPassword => do 
            putStr "Failure\n"
            pure () 
            