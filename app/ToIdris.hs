
{-# LANGUAGE NamedFieldPuns #-}

module ToIdris where 

    import FirstTypes

    uProg :: Prog -> String 
    uProg Prog {types, funcs} = 
        concatMap uTypes types ++ concatMap uFuncs funcs 

    uFuncs :: Func -> String 
    uFuncs = undefined 

    uTypes :: Decl -> String 
    uTypes = undefined 
    
