data Tree : (n : Nat) -> (a : Type) -> Type where 
	TEmpty : Tree 0 a
	Leaf : (val : a) -> Tree 1 a
	Branch : (left : Tree m a) -> (right : Tree n a) -> Tree (m + n) a


{n : Nat} -> {a : Type} -> ((DecEq a)) => DecEq ((Tree n a)) where 
	decEq (TEmpty) (TEmpty) = (Yes Refl)
	decEq (Leaf val1) (Leaf val2) with (decEq val1 val2)
		decEq (Leaf val1) (Leaf val1) | (Yes Refl)  = (Yes Refl)
		decEq (Leaf val1) (Leaf val2) | (No prf)  = (No (\h => (prf (case (h) of
			((Refl)) => (Refl)))))
	decEq (Branch left1 right1) (Branch left2 right2) with (decEq left1 left2)
		decEq (Branch left1 right1) (Branch left1 right2) | (Yes Refl)  with (decEq right1 right2)
			decEq (Branch left1 right1) (Branch left1 right1) | (Yes Refl) | (Yes Refl)  = (Yes Refl)
			decEq (Branch left1 right1) (Branch left1 right2) | (Yes Refl) | (No prf)  = (No (\h => (prf (case (h) of
				((Refl)) => (Refl)))))
		decEq (Branch left1 right1) (Branch left2 right2) | (No prf)  = (No (\h => (prf (case (h) of
			((Refl)) => (Refl)))))

