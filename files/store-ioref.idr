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

initStore : IO (IORef DStore)
initStore = newIORef $ MkDStore { secret="secret data :O\n", pub="public data\n" }

run : IORef DStore -> Store t st1 st2 -> IO t
run store Login = do
  putStr "enter password: "
  pw <- getLine
  if pw == "password123"
    then do
      pure OK
    else do
      pure BadPassword  
run store Logout = do 
    putStrLn "logging out"
    pure () 
run store ReadSecret = do 
    store <- readIORef store
    pure store.secret
run store (Pure x) = pure x
run store (Lift io) = io
run store (action >>= cont) = do 
    res <- run store action
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
            
main : IO ()
main = do 
    st <- initStore 
    _ <- run st main'
    pure ()