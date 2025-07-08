data Test3 : (n : Nat) -> (t : Type) -> Type where 
	CTest3 : (n : Nat) -> (x : t) -> (xs : Test3 n t) -> Test3 (S n) t


{n : Nat} -> {t : Type} -> ((DecEq t)) => DecEq ((Test3 n t)) where 
	decEq ((CTest3 n x1 xs1)) ((CTest3 n x2 xs2)) with (decEq x1 x2)
		decEq ((CTest3 n x1 xs1)) ((CTest3 n x1 xs2)) | (Yes Refl)  with (decEq xs1 xs2)
			decEq ((CTest3 n x1 xs1)) ((CTest3 n x1 xs1)) | (Yes Refl) | (Yes Refl)  = (Yes Refl)
			decEq ((CTest3 n x1 xs1)) ((CTest3 n x1 xs2)) | (Yes Refl) | (No prf)  = (No (\h => (prf (case (h) of
				((Refl)) => (Refl)))))
		decEq ((CTest3 n x1 xs1)) ((CTest3 n x2 xs2)) | (No prf)  = (No (\h => (prf (case (h) of
			((Refl)) => (Refl)))))

