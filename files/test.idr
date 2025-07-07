data Vect : (n : Nat) -> (t : Type) -> Type where 
	Nil : Vect 0 t
	Cons : (head : t) -> (tail : Vect n t) -> Vect (S n) t


(DecEq t) => DecEq (Vect n t) where 
	decEq (Nil) (Nil) = Yes Refl
	decEq (Cons head1 tail1) (Cons head2 tail2) with (decEq head1 head2)
		decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl  with (decEq tail1 tail2)
			decEq (Cons head1 tail1) (Cons head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (Cons head1 tail1) (Cons head2 tail2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

