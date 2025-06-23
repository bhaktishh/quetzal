module Test

data Vect : (t : Type) -> (n : Nat) -> Type where 
	Nil : Vect t 0
	Cons : (head : t) -> (tail : Vect t n) -> Vect t (S n)


data Pair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
	MkPair : (x : a) -> (y : (p t)) -> Pair a p


record DPairRec (t : Type) (p : (a : t) -> Type) where 
	constructor MkDPairRec
	fst : t
	snd : (p fst)


add5 : (x : Nat) -> Nat
add5 x = 
	let x = (x + 5) in
		x

test : ()
test  = 
	()

append : {n : Nat} -> {m : Nat} -> {t : Type} -> (v1 : Vect t n) -> (v2 : Vect t m) -> Vect t (n + m)
append v1 v2 = 
	case (v1,v2) of
		((Nil),v2) => v2
		((Cons x xs),v2) => let v2 = (append xs v2) in
			(Cons x v2)

replicate : {t : Type} -> (x : t) -> (n : Nat) -> Vect t n
replicate x n = 
	case (n) of
		(0) => Nil
		((S n)) => Cons x (replicate x n)

testLoop : (n : Nat) -> Nat
testLoop n = 
	let x : Nat = 11 in
		let x = 12 in
			if (x < 10) then 
				(testLoop_rec n)
			else 
				let n = (n + 2) in
					(n + 4)
where 
	testLoop_rec : (n : Nat) -> Nat
	testLoop_rec n = 
		if not (n < 10) then 
			let n = (n + 1) in
				n
		else 
			let n = (n + 4) in
				(testLoop_rec n)

