data Vect : (t : Type) -> (n : Nat) -> Type where 
Nil : Vect t 0
Cons : (head : t) -> (tail : Vect t n) -> Vect t (n + 1)
