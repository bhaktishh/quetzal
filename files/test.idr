data MyPair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
	MkMyPair : (x : a) -> (y : (p x)) -> MyPair a p


(DecEq a,(x : a) -> DecEq (p x)) => DecEq (MyPair a p) where 
	decEq (MkMyPair x1 y1) (MkMyPair x2 y2) with (decEq x1 x2)
		decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl  with (decEq y1 y2)
			decEq (MkMyPair x1 y1) (MkMyPair x1 y1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (MkMyPair x1 y1) (MkMyPair x2 y2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

