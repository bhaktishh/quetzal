
ref : IO (IORef String)
ref = newIORef "hi"

mod : IORef String -> IO () 
mod iostr = writeIORef iostr "bye"

f : IO () 
f = do 
    str <- ref 
    putStrLn !(readIORef str) 
    _ <- mod str 
    putStrLn !(readIORef str)
    pure ()