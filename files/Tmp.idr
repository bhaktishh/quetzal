import Decidable.Equality
data TestData : (t : Type) -> (i : Nat) -> Type where 
	C1 : (a : t) -> (ma : Maybe t) -> TestData t 0
	C2 : (b : u) -> (n : Nat) -> TestData u n
	C3 : (a : t) -> (lma : Maybe (List t)) -> TestData t 1


{t : Type} -> {i : Nat} -> DecEq t => DecEq (TestData t i) where 
	decEq (C1 a1 ma1) (C1 a2 ma2) with (decEq a1 a2)
		decEq (C1 a1 ma1) (C1 a1 ma2) | Yes Refl  with (decEq ma1 ma2)
			decEq (C1 a1 ma1) (C1 a1 ma1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (C1 a1 ma1) (C1 a1 ma2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (C1 a1 ma1) (C1 a2 ma2) | No prf  = No (\h => prf (case h of
			Refl => Refl))
	decEq (C1 a1 ma1) (C2 b2 n) = No (\h => case h of Refl impossible)
	decEq (C2 b1 n) (C1 a2 ma2) = No (\h => case h of Refl impossible)
	decEq (C2 b1 n) (C2 b2 n) with (decEq b1 b2)
		decEq (C2 b1 n) (C2 b1 n) | Yes Refl  = Yes Refl
		decEq (C2 b1 n) (C2 b2 n) | No prf  = No (\h => prf (case h of
			Refl => Refl))
	decEq (C2 b1 n) (C3 a2 lma2) = No (\h => case h of Refl impossible)
	decEq (C3 a1 lma1) (C2 b2 n) = No (\h => case h of Refl impossible)
	decEq (C3 a1 lma1) (C3 a2 lma2) with (decEq a1 a2)
		decEq (C3 a1 lma1) (C3 a1 lma2) | Yes Refl  with (decEq lma1 lma2)
			decEq (C3 a1 lma1) (C3 a1 lma1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (C3 a1 lma1) (C3 a1 lma2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (C3 a1 lma1) (C3 a2 lma2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

