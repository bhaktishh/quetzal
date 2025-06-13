module Test



	data Vect : (t : Type) -> (n : Nat) -> Type where 
		Nil : Vect t 0
		Cons : (head : t) -> (tail : Vect t n) -> Vect t (S n)

	append : {n : Nat} -> {m : Nat} -> {t : Type} -> (v1 : Vect t n) -> (v2 : Vect t m) -> Vect t (n + m)
	append Nil v2 = v2
	append (Cons x xs) v2 = Cons x (append xs v2)
