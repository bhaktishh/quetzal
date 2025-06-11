data Vect : (t : Type) -> (n : Nat) -> Type where 
	Nil : Vect T  0
	Cons : (head : T ) -> (tail : Vect T  n) -> Vect T  (n + 1)

data Pair : (t : Type) -> (p : ((a : T ) -> Type)) -> Type where 
	MkPair : (a : T ) -> (snd : P ) -> Pair T  p

record Pair : (t : Type) -> (p : ((a : T ) -> Type)) -> where 
	constructor MkPair
	fst : T 
	snd : p fst

append : (n : Nat) -> (m : Nat) -> (t : Type) -> (v1 : Vect T  n) -> (v2 : Vect T  m) -> Vect T  (n + m)
append n m t v1 v2 = let x : Nat = 5 in
	x
test : ()
test  = ()
