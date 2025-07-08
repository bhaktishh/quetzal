import Decidable.Equality

data Vect : (n : Nat) -> (t : Type) -> Type where 
	Nil : Vect 0 t
	Cons : (head : t) -> (tail : Vect n t) -> Vect (S n) t


{n : Nat} -> {t : Type} -> (DecEq t) => DecEq (Vect n t) where 
	decEq (Nil) (Nil) = Yes Refl
	decEq (Cons head1 tail1) (Cons head2 tail2) with (decEq head1 head2)
		decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl  with (decEq tail1 tail2)
			decEq (Cons head1 tail1) (Cons head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (Cons head1 tail1) (Cons head2 tail2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

data Test : (a : Type) -> (z : Type) -> (p : (z : Type) -> (a : x) -> Type) -> Type where 
	MkTest : (x : a) -> (z : Type) -> (pf : (p z x)) -> Test a z p


{a : Type} -> {z : Type} -> {p : (z : Type) -> (a : x) -> Type} -> (DecEq a) => (DecEq z) => ((z : Type) -> (a : x) -> DecEq (p z a)) => DecEq (Test a z p) where 
	decEq (MkTest x1 z pf1) (MkTest x2 z pf2) with (decEq x1 x2)
		decEq (MkTest x1 z pf1) (MkTest x1 z pf2) | Yes Refl  with (decEq pf1 pf2)
			decEq (MkTest x1 z pf1) (MkTest x1 z pf1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MkTest x1 z pf1) (MkTest x1 z pf2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (MkTest x1 z pf1) (MkTest x2 z pf2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

data MyPair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
	MkMyPair : (x : a) -> (y : (p x)) -> MyPair a p


{a : Type} -> {p : (x : a) -> Type} -> (DecEq a) => ((x : a) -> DecEq (p x)) => DecEq (MyPair a p) where 
	decEq (MkMyPair x1 y1) (MkMyPair x2 y2) with (decEq x1 x2)
		decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl  with (decEq y1 y2)
			decEq (MkMyPair x1 y1) (MkMyPair x1 y1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (MkMyPair x1 y1) (MkMyPair x2 y2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

data MyCurse : (a : Type) -> (b : (x : a) -> Type) -> (p : (x : a) -> (y : (b x)) -> Type) -> Type where 
	MkMyCurse : {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (x : a) -> (y : (b x)) -> (pf : (p x y)) -> MyCurse a b p


{a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (DecEq a) => ((x : a) -> DecEq (b x)) => ((x : a) -> (y : (b x)) -> DecEq (p x y)) => DecEq (MyCurse a b p) where 
	decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) with (decEq x1 x2)
		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl  with (decEq y1 y2)
			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl  with (decEq pf1 pf2)
				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf1) | Yes Refl | Yes Refl | Yes Refl  = Yes Refl
				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl | No prf  = No (\h => (prf (case (h) of
					(Refl) => Refl)))
			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

data MyEither : (a : Type) -> (b : Type) -> Type where 
	MyLeft : (x : a) -> MyEither a b
	MyRight : (y : b) -> MyEither a b


{a : Type} -> {b : Type} -> (DecEq a) => (DecEq b) => DecEq (MyEither a b) where 
	decEq (MyLeft x1) (MyLeft x2) with (decEq x1 x2)
		decEq (MyLeft x1) (MyLeft x1) | Yes Refl  = Yes Refl
		decEq (MyLeft x1) (MyLeft x2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))
	decEq (MyLeft x1) (MyRight y2) = No (\h => (case (h) of (Refl) impossible))
	decEq (MyRight y1) (MyLeft x2) = No (\h => (case (h) of (Refl) impossible))
	decEq (MyRight y1) (MyRight y2) with (decEq y1 y2)
		decEq (MyRight y1) (MyRight y1) | Yes Refl  = Yes Refl
		decEq (MyRight y1) (MyRight y2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

data Test3 : (s : Bool) -> Type where 
	C3 : (s : Bool) -> Test3 s


{s : Bool} -> DecEq (Test3 s) where 
	decEq (C3 s) (C3 s) = Yes Refl

data Test2 : (t : Type) -> Type where 
	C2 : (s : Bool) -> Test2 t


{t : Type} -> (DecEq t) => DecEq (Test2 t) where 
	decEq (C2 s1) (C2 s2) with (decEq s1 s2)
		decEq (C2 s1) (C2 s1) | Yes Refl  = Yes Refl
		decEq (C2 s1) (C2 s2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))



-- data BadExample : (n : Nat) -> (t : Type) -> Type where 
-- 	BadConstructor : (head : t) -> (n : Nat) -> BadExample n t

-- {n : Nat} -> {t : Type} -> DecEq t => DecEq (BadExample n t) where
-- 	decEq (BadConstructor head1 n1) (BadConstructor head2 n1) with (decEq head1 head2)
-- 		decEq (BadConstructor head1 n1) (BadConstructor head1 n2) | Yes Refl = Yes Refl
-- 		decEq (BadConstructor head1 n1) (BadConstructor head2 n2) | No prf  = No (\h => (prf (case (h) of
-- 				(Refl) => Refl)))

-- data BEx2 : (t : Type) -> (n : Nat) -> Type where
-- 	BC2 : (n : Nat) -> (head : t) -> BEx2 t n 

-- {t : Type} -> {n : Nat} -> DecEq t => DecEq (BEx2 t n) where
-- 	decEq (BC2 n1 head1) (BC2 n1 head2) with (decEq head1 head2)
-- 		decEq (BC2 n1 head1) (BC2 n1 head1) | Yes Refl = Yes Refl
-- 		decEq (BC2 n1 head1) (BC2 n1 head2) | No prf  = No (\h => (prf (case (h) of
-- 				(Refl) => Refl)))

-- data BEx3 : (t : Type) -> Type where
-- 	BC3 : (x : t) -> BEx3 t

-- {t : Type} -> DecEq t => DecEq (BEx3 t) where
-- 	decEq (BC3 x1) (BC3 x2) with (decEq x1 x2)
-- 		decEq (BC3 x1) (BC3 x1) | Yes Refl = Yes Refl 
-- 		decEq (BC3 x1) (BC3 x2) | No prf = No (\h => prf (case h of Refl => Refl))

-- -- data Test1 : (y : Type) -> (s : y) -> Type where 
-- -- 	C1 : (s : y) -> Test1 y s

-- -- {y : Type} -> {s : y} -> {t : Type} -> (DecEq t) => DecEq (Test1 y s) where 
-- -- 	decEq (C1 s1) (C1 s2) with (decEq s1 s2)
-- -- 		decEq (C1 s1) (C1 s1) | Yes Refl  = Yes Refl
-- -- 		decEq (C1 s1) (C1 s2) | No prf  = No (\h => (prf (case (h) of
-- -- 			(Refl) => Refl)))

-- data Vect : (n : Nat) -> (t : Type) -> Type where 
-- 	Nil : Vect 0 t
-- 	Cons : (head : t) -> (tail : Vect n t) -> Vect (S n) t


-- {n : Nat} -> {t : Type} -> (DecEq t) => DecEq (Vect n t) where 
-- 	decEq (Nil) (Nil) = Yes Refl
-- 	decEq (Cons head1 tail1) (Cons head2 tail2) with (decEq head1 head2)
-- 		decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl  with (decEq tail1 tail2)
-- 			decEq (Cons head1 tail1) (Cons head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
-- 			decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- 				(Refl) => Refl)))
-- 		decEq (Cons head1 tail1) (Cons head2 tail2) | No prf  = No (\h => (prf (case (h) of
-- 			(Refl) => Refl)))

-- data Test : (a : Type) -> (z : Type) -> (p : (z : Type) -> (a : x) -> Type) -> Type where 
-- 	MkTest : (x : a) -> (z : Type) -> (pf : (p z x)) -> Test a z p


-- {a : Type} -> {z : Type} -> {p : (z : Type) -> (a : x) -> Type} -> (DecEq a, DecEq z, (z : Type) -> (a : x) -> DecEq (p z a)) => DecEq (Test a z p) where 
-- 	decEq (MkTest x1 z pf1) (MkTest x2 z pf2) with (decEq x1 x2)
-- 		decEq (MkTest x1 z pf1) (MkTest x1 z pf2) | Yes Refl  with (decEq pf1 pf2)
-- 			decEq (MkTest x1 z pf1) (MkTest x1 z pf1) | Yes Refl | Yes Refl  = Yes Refl
-- 			decEq (MkTest x1 z pf1) (MkTest x1 z pf2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- 				(Refl) => Refl)))
-- 		decEq (MkTest x1 z pf1) (MkTest x2 z pf2) | No prf  = No (\h => (prf (case (h) of
-- 			(Refl) => Refl)))

-- data MyPair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
-- 	MkMyPair : (x : a) -> (y : (p x)) -> MyPair a p


-- {a : Type} -> {p : (x : a) -> Type} -> (DecEq a, (x : a) -> DecEq (p x)) => DecEq (MyPair a p) where 
-- 	decEq (MkMyPair x1 y1) (MkMyPair x2 y2) with (decEq x1 x2)
-- 		decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl  with (decEq y1 y2)
-- 			decEq (MkMyPair x1 y1) (MkMyPair x1 y1) | Yes Refl | Yes Refl  = Yes Refl
-- 			decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- 				(Refl) => Refl)))
-- 		decEq (MkMyPair x1 y1) (MkMyPair x2 y2) | No prf  = No (\h => (prf (case (h) of
-- 			(Refl) => Refl)))

-- data MyCurse : (a : Type) -> (b : (x : a) -> Type) -> (p : (x : a) -> (y : (b x)) -> Type) -> Type where 
-- 	MkMyCurse : {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (x : a) -> (y : (b x)) -> (pf : (p x y)) -> MyCurse a b p


-- {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (DecEq a, (x : a) -> DecEq (b x), (x : a) -> (y : (b x)) -> DecEq (p x y)) => DecEq (MyCurse a b p) where 
-- 	decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) with (decEq x1 x2)
-- 		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl  with (decEq y1 y2)
-- 			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl  with (decEq pf1 pf2)
-- 				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf1) | Yes Refl | Yes Refl | Yes Refl  = Yes Refl
-- 				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- 					(Refl) => Refl)))
-- 			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- 				(Refl) => Refl)))
-- 		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) | No prf  = No (\h => (prf (case (h) of
-- 			(Refl) => Refl)))

-- data MyEither : (a : Type) -> (b : Type) -> Type where 
-- 	MyLeft : (x : a) -> MyEither a b
-- 	MyRight : (y : b) -> MyEither a b


-- {a : Type} -> {b : Type} -> (DecEq a, DecEq b) => DecEq (MyEither a b) where 
-- 	decEq (MyLeft x1) (MyLeft x2) with (decEq x1 x2)
-- 		decEq (MyLeft x1) (MyLeft x1) | Yes Refl  = Yes Refl
-- 		decEq (MyLeft x1) (MyLeft x2) | No prf  = No (\h => (prf (case (h) of
-- 			(Refl) => Refl)))
-- 	decEq (MyLeft x1) (MyRight y2) = No (\h => (case (h) of (Refl) impossible))
-- 	decEq (MyRight y1) (MyLeft x2) = No (\h => (case (h) of (Refl) impossible))
-- 	decEq (MyRight y1) (MyRight y2) with (decEq y1 y2)
-- 		decEq (MyRight y1) (MyRight y1) | Yes Refl  = Yes Refl
-- 		decEq (MyRight y1) (MyRight y2) | No prf  = No (\h => (prf (case (h) of
-- 			(Refl) => Refl)))










-- -- data VectBad : (n : Nat) -> (t : Type) -> Type where 
-- -- 	NilBad : VectBad 0 t
-- -- 	ConsBad : (head : t) -> (n : Nat) -> VectBad (S n) t


-- -- {n : Nat} -> {t : Type} -> (DecEq t) => DecEq (VectBad n t) where 
-- -- 	decEq (NilBad) (NilBad) = Yes Refl
-- -- 	decEq (ConsBad head1 n) (ConsBad head2 n) with (decEq head1 head2)
-- -- 		decEq (ConsBad head1 n) (ConsBad head1 n) | Yes Refl = Yes Refl
-- -- 		decEq (ConsBad head1 n) (ConsBad head2 n) | No prf  = No (\h => (prf (case (h) of
-- -- 			(Refl) => Refl)))

-- -- 	-- decEq (ConsBad head1 n1) (ConsBad head2 n2) with (decEq head1 head2)
-- -- 	-- 	decEq (ConsBad head1 n1) (ConsBad head1 n2) | Yes Refl  with (decEq n1 n2)
-- -- 	-- 		decEq (ConsBad head1 n1) (ConsBad head1 n1) | Yes Refl | Yes Refl  = Yes Refl
-- -- 	-- 		decEq (ConsBad head1 n1) (ConsBad head1 n2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- 	-- 			(Refl) => Refl)))
-- -- 	-- 	decEq (ConsBad head1 n1) (ConsBad head2 n2) | No prf  = No (\h => (prf (case (h) of
-- -- 	-- 		(Refl) => Refl)))

-- -- data Test2 : (t : Type) -> Type where 
-- -- 	C2 : (s : Bool) -> Test2 t

-- -- {t : Type} -> (DecEq t) => DecEq (Test2 t) where 
-- -- 	decEq (C2 s1) (C2 s2) with (decEq s1 s2)
-- -- 		decEq (C2 s1) (C2 s1) | Yes Refl  = Yes Refl
-- -- 		decEq (C2 s1) (C2 s2) | No prf  = No (\h => (prf (case (h) of
-- -- 			(Refl) => Refl)))


-- -- data Vect : (n : Nat) -> (t : Type) -> Type where 
-- -- 	Nil : Vect 0 t
-- -- 	Cons : (head : t) -> (tail : Vect n t) -> Vect (S n) t

-- -- {n : Nat} -> {t : Type} -> (DecEq t) => DecEq (Vect n t) where 
-- -- 	decEq (Nil) (Nil) = Yes Refl
-- -- 	decEq (Cons head1 tail1) (Cons head2 tail2) with (decEq head1 head2)
-- -- 		decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl  with (decEq tail1 tail2)
-- -- 			decEq (Cons head1 tail1) (Cons head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
-- -- 			decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- 				(Refl) => Refl)))
-- -- 		decEq (Cons head1 tail1) (Cons head2 tail2) | No prf  = No (\h => (prf (case (h) of
-- -- 			(Refl) => Refl)))

-- -- data MyEither : (a : Type) -> (b : Type) -> Type where 
-- -- 	MyLeft : (x : a) -> MyEither a b
-- -- 	MyRight : (y : b) -> MyEither a b


-- -- {a : Type} -> {b : Type} -> (DecEq a, DecEq b) => DecEq (MyEither a b) where 
-- -- 	decEq (MyLeft x1) (MyLeft x2) with (decEq x1 x2)
-- -- 		decEq (MyLeft x1) (MyLeft x1) | Yes Refl  = Yes Refl
-- -- 		decEq (MyLeft x1) (MyLeft x2) | No prf  = No (\h => (prf (case (h) of
-- -- 			(Refl) => Refl)))
-- -- 	decEq (MyLeft x1) (MyRight y2) = No (\h => (case (h) of (Refl) impossible))
-- -- 	decEq (MyRight y1) (MyLeft x2) = No (\h => (case (h) of (Refl) impossible))
-- -- 	decEq (MyRight y1) (MyRight y2) with (decEq y1 y2)
-- -- 		decEq (MyRight y1) (MyRight y1) | Yes Refl  = Yes Refl
-- -- 		decEq (MyRight y1) (MyRight y2) | No prf  = No (\h => (prf (case (h) of
-- -- 			(Refl) => Refl)))





-- -- -- -- record DPairRec (t : Type) (p : (a : t) -> Type) where 
-- -- -- -- 	constructor MkDPairRec
-- -- -- -- 	fst : t
-- -- -- -- 	snd : (p fst)

-- -- -- -- {t : Type} -> {p : (a : t) -> Type} -> (DecEq t, (a : t) -> DecEq (p a)) => DecEq (DPairRec t p) where 
-- -- -- -- 	decEq (MkDPairRec fst1 snd1) (MkDPairRec fst2 snd2) with (decEq fst1 fst2)
-- -- -- -- 		decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd2) | Yes Refl with (decEq snd1 snd2)
-- -- -- -- 			decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd1) | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 			decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd2) | Yes Refl | No prf = No (\h => (prf (case h of Refl => Refl)))
-- -- -- -- 		decEq (MkDPairRec fst1 snd1) (MkDPairRec fst2 snd2) | No prf = No (\h => (prf (case h of Refl => Refl)))

-- -- -- record DPairRec (t : Type) (p : (a : t) -> Type) where 
-- -- -- 	constructor MkDPairRec
-- -- -- 	fst : t
-- -- -- 	snd : (p fst)


-- -- -- {t : Type} -> {p : (a : t) -> Type} -> (DecEq t, (a : t) -> DecEq (p a)) => DecEq (DPairRec t p) where 
-- -- -- 	decEq (MkDPairRec fst1 snd1) (MkDPairRec fst2 snd2) with (decEq fst1 fst2)
-- -- -- 		decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd2) | Yes Refl  with (decEq snd1 snd2)
-- -- -- 			decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd1) | Yes Refl | Yes Refl  = Yes Refl
-- -- -- 			decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- 				(Refl) => Refl)))
-- -- -- 		decEq (MkDPairRec fst1 snd1) (MkDPairRec fst2 snd2) | No prf  = No (\h => (prf (case (h) of
-- -- -- 			(Refl) => Refl)))



-- -- -- data Test : (a : Type) -> (z : Type) -> (p : (z : Type) -> (a : x) -> Type) -> Type where 
-- -- -- 	MkTest : (x : a) -> (z : Type) -> (pf : (p z x)) -> Test a z p


-- -- -- {a : Type} -> {z : Type} -> {p : (z : Type) -> (a : x) -> Type} -> (DecEq a, DecEq z, (z : Type) -> (a : x) -> DecEq (p z a)) => DecEq (Test a z p) where 
-- -- -- 	decEq (MkTest x1 z pf1) (MkTest x2 z pf2) with (decEq x1 x2)
-- -- -- 		decEq (MkTest x1 z pf1) (MkTest x1 z pf2) | Yes Refl  with (decEq pf1 pf2)
-- -- -- 			decEq (MkTest x1 z pf1) (MkTest x1 z pf1) | Yes Refl | Yes Refl  = Yes Refl
-- -- -- 			decEq (MkTest x1 z pf1) (MkTest x1 z pf2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- 				(Refl) => Refl)))
-- -- -- 		decEq (MkTest x1 z pf1) (MkTest x2 z pf2) | No prf  = No (\h => (prf (case (h) of
-- -- -- 			(Refl) => Refl)))

-- -- -- -- data Test : (a : Type) -> (b : Type) -> (p : Type -> (x : a) -> Type) -> Type where
-- -- -- -- 	MkTest : (x : a) -> (y : b) -> (z : Type) -> (pf : p z x) -> Test a b p 

-- -- -- data MyPair : (a : Type) -> (p : (x : 	a) -> Type) -> Type where 
-- -- -- 	MkMyPair : (x : a) -> (y : (p x)) -> MyPair a p


-- -- -- {a : Type} -> {p : (x : a) -> Type} -> (DecEq a, (x : a) -> DecEq (p x)) => DecEq (MyPair a p) where 
-- -- -- 		decEq (MkMyPair x1 y1) (MkMyPair x2 y2) with (decEq x1 x2)
-- -- -- 			decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl  with (decEq y1 y2)
-- -- -- 				decEq (MkMyPair x1 y1) (MkMyPair x1 y1) | Yes Refl | Yes Refl  = Yes Refl
-- -- -- 				decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- 					(Refl) => Refl)))
-- -- -- 			decEq (MkMyPair x1 y1) (MkMyPair x2 y2) | No prf  = No (\h => (prf (case (h) of
-- -- -- 				(Refl) => Refl)))

-- -- -- data MyCurse : (a : Type) -> (b : (x : 		a) -> Type) -> (p : (x : a) -> (y : (b x)) -> Type) -> Type where 
-- -- -- 	MkMyCurse : {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (x : a) -> (y : (b x)) -> (pf : (p x y)) -> MyCurse a b p


-- -- -- {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (DecEq a, (x : a) -> DecEq (b x), (x : a) -> (y : (b x)) -> DecEq (p x y)) => DecEq (MyCurse a b p) where 
-- -- -- 			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) with (decEq x1 x2)
-- -- -- 				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl  with (decEq y1 y2)
-- -- -- 					decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl  with (decEq pf1 pf2)
-- -- -- 						decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf1) | Yes Refl | Yes Refl | Yes Refl  = Yes Refl
-- -- -- 						decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- 							(Refl) => Refl)))
-- -- -- 					decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- 						(Refl) => Refl)))
-- -- -- 				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) | No prf  = No (\h => (prf (case (h) of
-- -- -- 					(Refl) => Refl)))


-- -- -- -- data MyPair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
-- -- -- -- 	MkMyPair : (x : a) -> (pf : p x) -> MyPair a p

-- -- -- -- data MyCurse : (a : Type) -> (b : (x : a) -> Type) -> (p : (x : a) -> (y : b x) -> Type) -> Type where
-- -- -- -- 	MkMyCurse : {a : _} -> {b : a -> _} -> {p : a -> _} -> (x : a) -> (y : b x) -> (pf : p x y) -> MyCurse a b p

-- -- -- -- data MyCurse : (a : Type) -> (b : (x : a) -> Type) -> (p : (x : a) -> (y : (b x)) -> Type) -> Type where 
-- -- -- -- 	MkMyCurse : {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (x : a) -> (y : (b x)) -> (pf : (p x y)) -> MyCurse a b p


-- -- -- -- {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : (b x)) -> Type} -> (DecEq a, (x : a) -> DecEq (b x), (x : a) -> (y : (b x)) -> DecEq (p x y)) => DecEq (MyCurse a b p) where 
-- -- -- -- 	decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) with (decEq x1 x2)
-- -- -- -- 		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl  with (decEq y1 y2)
-- -- -- -- 			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl  with (decEq pf1 pf2)
-- -- -- -- 				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf1) | Yes Refl | Yes Refl | Yes Refl  = Yes Refl
-- -- -- -- 				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 					(Refl) => Refl)))
-- -- -- -- 			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 				(Refl) => Refl)))
-- -- -- -- 		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 			(Refl) => Refl)))

-- -- -- -- implementation (DecEq a, (x : a) -> DecEq (b x), (x : a) -> (y : b x) -> DecEq (p x y)) => DecEq (MyCurse a b p) where

-- -- -- -- fstInjective : (MkMyPair x px = MkMyPair y py) -> x = y
-- -- -- -- fstInjective Refl = Refl 

-- -- -- -- sndInjective : {x : a} -> {y : a} -> {px : p x} -> {py : p y} -> (MkMyPair {p = p} x px = MkMyPair {p = p} y py) -> (px = py)
-- -- -- -- sndInjective Refl = Refl

-- -- -- -- implementation (DecEq a, (x : a) -> DecEq (p x)) => DecEq (MyPair a p) where 
-- -- -- -- 	decEq (MkMyPair x px) (MkMyPair y py) with (decEq x y) 
-- -- -- -- 		decEq (MkMyPair x px) (MkMyPair x py) | Yes Refl with (decEq px py)
-- -- -- -- 			decEq (MkMyPair x px) (MkMyPair x px) | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 			decEq (MkMyPair x px) (MkMyPair x py) | (Yes Refl) | (No prf) = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 		decEq (MkMyPair x px) (MkMyPair y py) | No prf = No $ (\h => prf (case h of Refl => Refl))

-- -- -- -- data MyPair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
-- -- -- -- 	MkMyPair : (x : a) -> (y : (p x)) -> MyPair a p


-- -- -- -- (DecEq a,(x : a) -> DecEq (p x)) => DecEq (MyPair a p) where 
-- -- -- -- 	decEq (MkMyPair x1 y1) (MkMyPair x2 y2) with (decEq x1 x2)
-- -- -- -- 		decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl  with (decEq y1 y2)
-- -- -- -- 			decEq (MkMyPair x1 y1) (MkMyPair x1 y1) | Yes Refl | Yes Refl  = Yes Refl
-- -- -- -- 			decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 				(Refl) => Refl)))
-- -- -- -- 		decEq (MkMyPair x1 y1) (MkMyPair x2 y2) | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 			(Refl) => Refl)))

-- -- -- -- data MyVect : (n : Nat) -> (t : Type) -> Type where 
-- -- -- -- 	MyNil : MyVect 0 t
-- -- -- -- 	MyCons : (head : t) -> (tail : MyVect n t) -> MyVect (S n) t

-- -- -- -- consHeadInjective : (MyCons h1 t1 = MyCons h2 t2) -> h1 = h2
-- -- -- -- consHeadInjective Refl = Refl

-- -- -- -- consTailInjective : (MyCons h1 t1 = MyCons h2 t2) -> t1 = t2
-- -- -- -- consTailInjective Refl = Refl

-- -- -- -- (DecEq t) => DecEq (MyVect n t) where 
-- -- -- -- 	decEq MyNil MyNil = Yes Refl 
-- -- -- -- 	decEq (MyCons h1 t1) (MyCons h2 t2) with (decEq h1 h2)
-- -- -- -- 		decEq (MyCons h1 t1) (MyCons h1 t2) | Yes Refl with (decEq t1 t2) 
-- -- -- -- 			decEq (MyCons h1 t1) (MyCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 			decEq (MyCons h1 t1) (MyCons h1 t2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 		decEq (MyCons h1 t1) (MyCons h2 t2) | No prf = No $ (\h => prf (case h of Refl => Refl))

-- -- -- -- (DecEq t) => DecEq (MyVect n t) where 
-- -- -- -- 	decEq MyNil MyNil = Yes Refl 
-- -- -- -- 	decEq (MyCons h1 t1) (MyCons h2 t2) with (decEq h1 h2) | (decEq t1 t2) 
-- -- -- -- 			decEq (MyCons h1 t1) (MyCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 			decEq (MyCons h1 t1) (MyCons h1 t2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 			decEq (MyCons h1 t1) (MyCons h2 t2) | No prf | _ = No $ (\h => prf (case h of Refl => Refl))

-- -- -- -- data MyList : (t : Type) -> Type where
-- -- -- -- 	MyListNil : MyList t
-- -- -- -- 	MyListCons : (head : t) -> (tail : MyList t) -> MyList t

-- -- -- -- (DecEq t) => DecEq (MyList t) where
-- -- -- -- 	decEq MyListNil MyListNil = Yes Refl 
-- -- -- -- 	decEq (MyListCons h1 t1) (MyListCons h2 t2) with (decEq h1 h2)
-- -- -- -- 		decEq (MyListCons h1 t1) (MyListCons h1 t2) | Yes Refl with (decEq t1 t2)
-- -- -- -- 			decEq (MyListCons h1 t1) (MyListCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 			decEq (MyListCons h1 t1) (MyListCons h1 t2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 		decEq (MyListCons h1 t1) (MyListCons h2 t2) | No prf = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 	decEq MyListNil (MyListCons h t) = No (\h => (case h of Refl impossible ))
-- -- -- -- 	decEq (MyListCons h t) MyListNil = No (\h => (case h of Refl impossible ))

-- -- -- -- (DecEq t) => DecEq (MyList t) where
-- -- -- -- 	decEq MyListNil MyListNil = Yes Refl 
-- -- -- -- 	decEq (MyListCons h1 t1) (MyListCons h2 t2) with (decEq h1 h2) | (decEq t1 t2)
-- -- -- -- 		decEq (MyListCons h1 t1) (MyListCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 		decEq (MyListCons h1 t1) (MyListCons h2 t2) | _ | No prf = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 		decEq (MyListCons h1 t1) (MyListCons h2 t2) | No prf | _ = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 	decEq MyListNil (MyListCons _ _) = No (\h => (case h of Refl impossible ))
-- -- -- -- 	decEq (MyListCons _ _) MyListNil = No (\h => (case h of Refl impossible ))

-- -- -- -- (DecEq t) => DecEq (MyList t) where 
-- -- -- -- 	decEq (MyListNil) (MyListNil) = Yes Refl
-- -- -- -- 	decEq (MyListNil) (MyListCons head2 tail2) = No (\h => (case (h) of (Refl) impossible))
-- -- -- -- 	decEq (MyListCons head1 tail1) (MyListNil) = No (\h => (case (h) of (Refl) impossible))
-- -- -- -- 	decEq (MyListCons head1 tail1) (MyListCons head2 tail2) with (decEq head1 head2)
-- -- -- -- 		decEq (MyListCons head1 tail1) (MyListCons head1 tail2) | Yes Refl  with (decEq tail1 tail2)
-- -- -- -- 			decEq (MyListCons head1 tail1) (MyListCons head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
-- -- -- -- 			decEq (MyListCons head1 tail1) (MyListCons head1 tail2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 				(Refl) => Refl)))
-- -- -- -- 		decEq (MyListCons head1 tail1) (MyListCons head2 tail2) | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 			(Refl) => Refl)))

-- -- -- -- data SoManyArgs : (t : Type) -> Type where 
-- -- -- -- 	MyC : (a : t) -> (b : t) -> (c : t) -> (d : t) -> SoManyArgs t

-- -- -- -- data LessArgs : (t : Type) -> Type where 
-- -- -- -- 	MyC2 : (a : t) -> (b : t) -> LessArgs t

-- -- -- -- (DecEq t) => DecEq (LessArgs t) where
-- -- -- -- 	decEq (MyC2 a1 b1) (MyC2 a2 b2) with (decEq a1 a2)
-- -- -- -- 		decEq (MyC2 a1 b1) (MyC2 a1 b2) | Yes Refl with (decEq b1 b2) 
-- -- -- -- 			decEq (MyC2 a1 b1) (MyC2 a1 b1) | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 			decEq (MyC2 a1 b1) (MyC2 a1 b2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 		decEq (MyC2 a1 b1) (MyC2 a2 b2) | No prf = No $ (\h => prf (case h of Refl => Refl))

-- -- -- -- (DecEq t) => DecEq (LessArgs t) where 
-- -- -- -- 	decEq (MyC2 a1 b1) (MyC2 a2 b2) with (decEq a1 a2)
-- -- -- -- 		decEq (MyC2 a1 b1) (MyC2 a1 b2) | Yes Refl  with (decEq b1 b2)
-- -- -- -- 			decEq (MyC2 a1 b1) (MyC2 a1 b1) | Yes Refl | Yes Refl  = Yes Refl
-- -- -- -- 			decEq (MyC2 a1 b1) (MyC2 a1 b2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 				(Refl) => Refl)))
-- -- -- -- 		decEq (MyC2 a1 b1) (MyC2 a2 b2) | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 			(Refl) => Refl)))

-- -- -- -- (DecEq t) => DecEq (SoManyArgs t) where
-- -- -- -- 	decEq (MyC a1 b1 c1) (MyC a2 b2 c2) with (decEq a1 a2)
-- -- -- -- 		decEq (MyC a1 b1 c1) (MyC a1 b2 c2) | Yes Refl with (decEq b1 b2) 
-- -- -- -- 			decEq (MyC a1 b1 c1) (MyC a1 b1 c2) | Yes Refl | Yes Refl with (decEq c1 c2)
-- -- -- -- 				decEq (MyC a1 b1 c1) (MyC a1 b1 c1) | Yes Refl | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 				decEq (MyC a1 b1 c1) (MyC a1 b1 c2) | Yes Refl | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 			decEq (MyC a1 b1 c1) (MyC a1 b2 c2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 		decEq (MyC a1 b1 c1) (MyC a2 b2 c2) | No prf = No $ (\h => prf (case h of Refl => Refl))

-- -- -- -- (DecEq t) => DecEq (SoManyArgs t) where 
-- -- -- -- 	decEq (MyC a1 b1 c1 d1) (MyC a2 b2 c2 d2) with (decEq a1 a2)
-- -- -- -- 		decEq (MyC a1 b1 c1 d1) (MyC a1 b2 c2 d2) | Yes Refl  with (decEq b1 b2)
-- -- -- -- 			decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c2 d2) | Yes Refl | Yes Refl  with (decEq c1 c2)
-- -- -- -- 				decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c1 d2) | Yes Refl | Yes Refl | Yes Refl  with (decEq d1 d2)
-- -- -- -- 					decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c1 d1) | Yes Refl | Yes Refl | Yes Refl | Yes Refl  = Yes Refl
-- -- -- -- 					decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c1 d2) | Yes Refl | Yes Refl | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 						(Refl) => Refl)))
-- -- -- -- 				decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c2 d2) | Yes Refl | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 					(Refl) => Refl)))
-- -- -- -- 			decEq (MyC a1 b1 c1 d1) (MyC a1 b2 c2 d2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 				(Refl) => Refl)))
-- -- -- -- 		decEq (MyC a1 b1 c1 d1) (MyC a2 b2 c2 d2) | No prf  = No (\h => (prf (case (h) of
-- -- -- -- 			(Refl) => Refl)))

-- -- -- -- (DecEq t) => DecEq (SoManyArgs t) where
-- -- -- -- 	decEq (MyC a1 b1 c1) (MyC a2 b2 c2) with (decEq a1 a2) | (decEq b1 b2) | (decEq c1 c2)
-- -- -- -- 		decEq (MyC a1 b1 c1 ) (MyC a1 b1 c1 ) | Yes Refl | Yes Refl | Yes Refl = Yes Refl 
-- -- -- -- 		decEq (MyC a1 b1 c1 ) (MyC a1 b1 c2 ) | Yes Refl | Yes Refl | No prf  = No $ (\h => prf (case h of Refl => Refl)) 
-- -- -- -- 		decEq (MyC a1 b1 c1 ) (MyC a1 b2 c1 ) | Yes Refl | No prf | Yes Refl = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 		decEq (MyC a1 b1 c1 ) (MyC a1 b2 c2 ) | Yes Refl | No prf1 | No prf2 = No $ (\h => prf1 (prf2 (case h of Refl => Refl)))
-- -- -- -- 		decEq (MyC a1 b1 c1 ) (MyC a2 b1 c1 ) | No prf | Yes Refl | Yes Refl = No $ (\h => prf (case h of Refl => Refl))
-- -- -- -- 		decEq (MyC a1 b1 c1 ) (MyC a2 b1 c2 ) | No prf1 | Yes Refl | No prf2 = No $ (\h => prf1 (prf2 (case h of Refl => Refl)))
-- -- -- -- 		decEq (MyC a1 b1 c1 ) (MyC a2 b2 c1 ) | No prf1 | No prf2 | Yes Refl = No $ (\h => prf1 (prf2 (case h of Refl => Refl)))
-- -- -- -- 		decEq (MyC a1 b1 c1 ) (MyC a2 b2 c2 ) | No prf1 | No prf2 | No prf3 = No $ (\h => prf1 (prf2 (prf3 (case h of Refl => Refl))))
-- -- -- -- import Data.Vect

-- -- -- -- import Data.Nat

-- -- -- -- import Decidable.Equality	
	

-- -- -- -- search : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> Maybe (Fin n)
-- -- -- -- search n ls x = 
-- -- -- -- 	let i : Nat = 0 in
-- -- -- -- 		let ret : Maybe (Fin n) = Nothing in
-- -- -- -- 			(search_rec0 n ls x i ret)
-- -- -- -- where 
-- -- -- -- 	search_rec0 : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> (i : Nat) -> (ret : Maybe (Fin n)) -> Maybe (Fin n)
-- -- -- -- 	search_rec0 n ls x i ret = 
-- -- -- -- 		case ((isLT i n)) of
-- -- -- -- 			(No noprf) => ret
-- -- -- -- 			(Yes yesprf) => case ((decEq (index (natToFinLT i) ls) x)) of
-- -- -- -- 				(Yes yesprf) => let i : Nat = (S i) in
-- -- -- -- 					(search_rec0 n ls x i ret)
-- -- -- -- 				(No noprf) => let ret : Maybe (Fin n) = (Just (natToFinLT i)) in
-- -- -- -- 					let i : Nat = (S i) in
-- -- -- -- 						(search_rec0 n ls x i ret)
