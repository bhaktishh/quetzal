data Vect : (t : Type) -> (n : Nat) -> Type where 
	Nil : Vect t 0
	Cons : (head : t) -> (tail : Vect t n) -> Vect t (n + 1)

record Pair (t : Type) -> (p : ((a : t) -> Type)) -> where 
	constructor MkPair
	fst : t
	snd : p fst

