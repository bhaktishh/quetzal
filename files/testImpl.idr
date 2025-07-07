(DecEq t) => DecEq (MyList t) where 
	decEq (MyListNil) (MyListNil) = Yes Refl
	decEq (MyListNil) (MyListCons head2 tail2) = No (\h => (case (h) of (Refl) impossible))
	decEq (MyListCons head1 tail1) (MyListNil) = No (\h => (case (h) of (Refl) impossible))
	decEq (MyListCons head1 tail1) (MyListCons head2 tail2) with (decEq head1 head2)
		decEq (MyListCons head1 tail1) (MyListCons head1 tail2) | Yes Refl  with (decEq tail1 tail2)
			decEq (MyListCons head1 tail1) (MyListCons head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MyListCons head1 tail1) (MyListCons head1 tail2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (MyListCons head1 tail1) (MyListCons head2 tail2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))