data Vect : Type -> Nat -> Type where
   Nil  : Vect t 0
   Cons : t -> Vect t n -> Vect t (n+1)