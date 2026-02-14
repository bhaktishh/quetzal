data SoManyArgs : (t : Type) -> Type where 
	C1 : (a : t) -> (b : t) -> (c : t) -> (d : t) -> SoManyArgs t
	C2 : (x : t) -> (y : t) -> SoManyArgs t


{t : Type} -> ((DecEq t)) => DecEq ((SoManyArgs t)) where 
	decEq (C1 a1 b1 c1 d1) (C1 a2 b2 c2 d2) with (decEq a1 a2)
		decEq (C1 a1 b1 c1 d1) (C1 a1 b2 c2 d2) | (Yes Refl)  with (decEq b1 b2)
			decEq (C1 a1 b1 c1 d1) (C1 a1 b1 c2 d2) | (Yes Refl) | (Yes Refl)  with (decEq c1 c2)
				decEq (C1 a1 b1 c1 d1) (C1 a1 b1 c1 d2) | (Yes Refl) | (Yes Refl) | (Yes Refl)  with (decEq d1 d2)
					decEq (C1 a1 b1 c1 d1) (C1 a1 b1 c1 d1) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (Yes Refl)  = (Yes Refl)
					decEq (C1 a1 b1 c1 d1) (C1 a1 b1 c1 d2) | (Yes Refl) | (Yes Refl) | (Yes Refl) | (No prf)  = (No (\h => (prf (case (h) of
						((Refl)) => (Refl)))))
				decEq (C1 a1 b1 c1 d1) (C1 a1 b1 c2 d2) | (Yes Refl) | (Yes Refl) | (No prf)  = (No (\h => (prf (case (h) of
					((Refl)) => (Refl)))))
			decEq (C1 a1 b1 c1 d1) (C1 a1 b2 c2 d2) | (Yes Refl) | (No prf)  = (No (\h => (prf (case (h) of
				((Refl)) => (Refl)))))
		decEq (C1 a1 b1 c1 d1) (C1 a2 b2 c2 d2) | (No prf)  = (No (\h => (prf (case (h) of
			((Refl)) => (Refl)))))
	decEq (C1 a1 b1 c1 d1) (C2 x2 y2) = (No (\h => (case (h) of ((Refl)) impossible)))
	decEq (C2 x1 y1) (C1 a2 b2 c2 d2) = (No (\h => (case (h) of ((Refl)) impossible)))
	decEq (C2 x1 y1) (C2 x2 y2) with (decEq x1 x2)
		decEq (C2 x1 y1) (C2 x1 y2) | (Yes Refl)  with (decEq y1 y2)
			decEq (C2 x1 y1) (C2 x1 y1) | (Yes Refl) | (Yes Refl)  = (Yes Refl)
			decEq (C2 x1 y1) (C2 x1 y2) | (Yes Refl) | (No prf)  = (No (\h => (prf (case (h) of
				((Refl)) => (Refl)))))
		decEq (C2 x1 y1) (C2 x2 y2) | (No prf)  = (No (\h => (prf (case (h) of
			((Refl)) => (Refl)))))

