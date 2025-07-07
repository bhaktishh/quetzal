import Decidable.Equality

data MyPair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
	MkMyPair : (x : a) -> (pf : p x) -> MyPair a p

-- data MyCurse : (a : Type) -> (b : (x : a) -> Type) -> (p : (x : a) -> (y : b x) -> Type) -> Type where
-- 	MkMyCurse : (x : a) -> (y : b x) -> (pf : p x y) -> MyCurse a b p

-- implementation (DecEq a, (x : a) -> DecEq (b x), (x : a) -> (y : b x) -> DecEq (p x y)) => DecEq (MyCurse a b p) where

-- fstInjective : (MkMyPair x px = MkMyPair y py) -> x = y
-- fstInjective Refl = Refl 

-- sndInjective : {x : a} -> {y : a} -> {px : p x} -> {py : p y} -> (MkMyPair {p = p} x px = MkMyPair {p = p} y py) -> (px = py)
-- sndInjective Refl = Refl

implementation (DecEq a, (x : a) -> DecEq (p x)) => DecEq (MyPair a p) where 
	decEq (MkMyPair x px) (MkMyPair y py) with (decEq x y) 
		decEq (MkMyPair x px) (MkMyPair x py) | Yes Refl with (decEq px py)
			decEq (MkMyPair x px) (MkMyPair x px) | Yes Refl | Yes Refl = Yes Refl 
			decEq (MkMyPair x px) (MkMyPair x py) | (Yes Refl) | (No prf) = No $ (\h => prf (case h of Refl => Refl))
		decEq (MkMyPair x px) (MkMyPair y py) | No prf = No $ (\h => prf (case h of Refl => Refl))

data MyVect : (n : Nat) -> (t : Type) -> Type where 
	MyNil : MyVect 0 t
	MyCons : (head : t) -> (tail : MyVect n t) -> MyVect (S n) t

-- consHeadInjective : (MyCons h1 t1 = MyCons h2 t2) -> h1 = h2
-- consHeadInjective Refl = Refl

-- consTailInjective : (MyCons h1 t1 = MyCons h2 t2) -> t1 = t2
-- consTailInjective Refl = Refl

-- (DecEq t) => DecEq (MyVect n t) where 
-- 	decEq MyNil MyNil = Yes Refl 
-- 	decEq (MyCons h1 t1) (MyCons h2 t2) with (decEq h1 h2)
-- 		decEq (MyCons h1 t1) (MyCons h1 t2) | Yes Refl with (decEq t1 t2) 
-- 			decEq (MyCons h1 t1) (MyCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
-- 			decEq (MyCons h1 t1) (MyCons h1 t2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- 		decEq (MyCons h1 t1) (MyCons h2 t2) | No prf = No $ (\h => prf (case h of Refl => Refl))

(DecEq t) => DecEq (MyVect n t) where 
	decEq MyNil MyNil = Yes Refl 
	decEq (MyCons h1 t1) (MyCons h2 t2) with (decEq h1 h2) | (decEq t1 t2) 
			decEq (MyCons h1 t1) (MyCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
			decEq (MyCons h1 t1) (MyCons h1 t2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
			decEq (MyCons h1 t1) (MyCons h2 t2) | No prf | _ = No $ (\h => prf (case h of Refl => Refl))

data MyList : (t : Type) -> Type where
	MyListNil : MyList t
	MyListCons : (head : t) -> (tail : MyList t) -> MyList t

-- (DecEq t) => DecEq (MyList t) where
-- 	decEq MyListNil MyListNil = Yes Refl 
-- 	decEq (MyListCons h1 t1) (MyListCons h2 t2) with (decEq h1 h2)
-- 		decEq (MyListCons h1 t1) (MyListCons h1 t2) | Yes Refl with (decEq t1 t2)
-- 			decEq (MyListCons h1 t1) (MyListCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
-- 			decEq (MyListCons h1 t1) (MyListCons h1 t2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- 		decEq (MyListCons h1 t1) (MyListCons h2 t2) | No prf = No $ (\h => prf (case h of Refl => Refl))
-- 	decEq MyListNil (MyListCons h t) = No (\h => (case h of Refl impossible ))
-- 	decEq (MyListCons h t) MyListNil = No (\h => (case h of Refl impossible ))

-- (DecEq t) => DecEq (MyList t) where
-- 	decEq MyListNil MyListNil = Yes Refl 
-- 	decEq (MyListCons h1 t1) (MyListCons h2 t2) with (decEq h1 h2) | (decEq t1 t2)
-- 		decEq (MyListCons h1 t1) (MyListCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
-- 		decEq (MyListCons h1 t1) (MyListCons h2 t2) | _ | No prf = No $ (\h => prf (case h of Refl => Refl))
-- 		decEq (MyListCons h1 t1) (MyListCons h2 t2) | No prf | _ = No $ (\h => prf (case h of Refl => Refl))
-- 	decEq MyListNil (MyListCons _ _) = No (\h => (case h of Refl impossible ))
-- 	decEq (MyListCons _ _) MyListNil = No (\h => (case h of Refl impossible ))

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

data SoManyArgs : (t : Type) -> Type where 
	MyC : (a : t) -> (b : t) -> (c : t) -> (d : t) -> SoManyArgs t

data LessArgs : (t : Type) -> Type where 
	MyC2 : (a : t) -> (b : t) -> LessArgs t

-- (DecEq t) => DecEq (LessArgs t) where
-- 	decEq (MyC2 a1 b1) (MyC2 a2 b2) with (decEq a1 a2)
-- 		decEq (MyC2 a1 b1) (MyC2 a1 b2) | Yes Refl with (decEq b1 b2) 
-- 			decEq (MyC2 a1 b1) (MyC2 a1 b1) | Yes Refl | Yes Refl = Yes Refl 
-- 			decEq (MyC2 a1 b1) (MyC2 a1 b2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- 		decEq (MyC2 a1 b1) (MyC2 a2 b2) | No prf = No $ (\h => prf (case h of Refl => Refl))

(DecEq t) => DecEq (LessArgs t) where 
	decEq (MyC2 a1 b1) (MyC2 a2 b2) with (decEq a1 a2)
		decEq (MyC2 a1 b1) (MyC2 a1 b2) | Yes Refl  with (decEq b1 b2)
			decEq (MyC2 a1 b1) (MyC2 a1 b1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MyC2 a1 b1) (MyC2 a1 b2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (MyC2 a1 b1) (MyC2 a2 b2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

-- (DecEq t) => DecEq (SoManyArgs t) where
-- 	decEq (MyC a1 b1 c1) (MyC a2 b2 c2) with (decEq a1 a2)
-- 		decEq (MyC a1 b1 c1) (MyC a1 b2 c2) | Yes Refl with (decEq b1 b2) 
-- 			decEq (MyC a1 b1 c1) (MyC a1 b1 c2) | Yes Refl | Yes Refl with (decEq c1 c2)
-- 				decEq (MyC a1 b1 c1) (MyC a1 b1 c1) | Yes Refl | Yes Refl | Yes Refl = Yes Refl 
-- 				decEq (MyC a1 b1 c1) (MyC a1 b1 c2) | Yes Refl | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- 			decEq (MyC a1 b1 c1) (MyC a1 b2 c2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
-- 		decEq (MyC a1 b1 c1) (MyC a2 b2 c2) | No prf = No $ (\h => prf (case h of Refl => Refl))

(DecEq t) => DecEq (SoManyArgs t) where 
	decEq (MyC a1 b1 c1 d1) (MyC a2 b2 c2 d2) with (decEq a1 a2)
		decEq (MyC a1 b1 c1 d1) (MyC a1 b2 c2 d2) | Yes Refl  with (decEq b1 b2)
			decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c2 d2) | Yes Refl | Yes Refl  with (decEq c1 c2)
				decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c1 d2) | Yes Refl | Yes Refl | Yes Refl  with (decEq d1 d2)
					decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c1 d1) | Yes Refl | Yes Refl | Yes Refl | Yes Refl  = Yes Refl
					decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c1 d2) | Yes Refl | Yes Refl | Yes Refl | No prf  = No (\h => (prf (case (h) of
						(Refl) => Refl)))
				decEq (MyC a1 b1 c1 d1) (MyC a1 b1 c2 d2) | Yes Refl | Yes Refl | No prf  = No (\h => (prf (case (h) of
					(Refl) => Refl)))
			decEq (MyC a1 b1 c1 d1) (MyC a1 b2 c2 d2) | Yes Refl | No prf  = No (\h => (prf (case (h) of
				(Refl) => Refl)))
		decEq (MyC a1 b1 c1 d1) (MyC a2 b2 c2 d2) | No prf  = No (\h => (prf (case (h) of
			(Refl) => Refl)))

-- (DecEq t) => DecEq (SoManyArgs t) where
-- 	decEq (MyC a1 b1 c1) (MyC a2 b2 c2) with (decEq a1 a2) | (decEq b1 b2) | (decEq c1 c2)
-- 		decEq (MyC a1 b1 c1 ) (MyC a1 b1 c1 ) | Yes Refl | Yes Refl | Yes Refl = Yes Refl 
-- 		decEq (MyC a1 b1 c1 ) (MyC a1 b1 c2 ) | Yes Refl | Yes Refl | No prf  = No $ (\h => prf (case h of Refl => Refl)) 
-- 		decEq (MyC a1 b1 c1 ) (MyC a1 b2 c1 ) | Yes Refl | No prf | Yes Refl = No $ (\h => prf (case h of Refl => Refl))
-- 		decEq (MyC a1 b1 c1 ) (MyC a1 b2 c2 ) | Yes Refl | No prf1 | No prf2 = No $ (\h => prf1 (prf2 (case h of Refl => Refl)))
-- 		decEq (MyC a1 b1 c1 ) (MyC a2 b1 c1 ) | No prf | Yes Refl | Yes Refl = No $ (\h => prf (case h of Refl => Refl))
-- 		decEq (MyC a1 b1 c1 ) (MyC a2 b1 c2 ) | No prf1 | Yes Refl | No prf2 = No $ (\h => prf1 (prf2 (case h of Refl => Refl)))
-- 		decEq (MyC a1 b1 c1 ) (MyC a2 b2 c1 ) | No prf1 | No prf2 | Yes Refl = No $ (\h => prf1 (prf2 (case h of Refl => Refl)))
-- 		decEq (MyC a1 b1 c1 ) (MyC a2 b2 c2 ) | No prf1 | No prf2 | No prf3 = No $ (\h => prf1 (prf2 (prf3 (case h of Refl => Refl))))
-- import Data.Vect

-- import Data.Nat

-- import Decidable.Equality	
	

-- search : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> Maybe (Fin n)
-- search n ls x = 
-- 	let i : Nat = 0 in
-- 		let ret : Maybe (Fin n) = Nothing in
-- 			(search_rec0 n ls x i ret)
-- where 
-- 	search_rec0 : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> (i : Nat) -> (ret : Maybe (Fin n)) -> Maybe (Fin n)
-- 	search_rec0 n ls x i ret = 
-- 		case ((isLT i n)) of
-- 			(No noprf) => ret
-- 			(Yes yesprf) => case ((decEq (index (natToFinLT i) ls) x)) of
-- 				(Yes yesprf) => let i : Nat = (S i) in
-- 					(search_rec0 n ls x i ret)
-- 				(No noprf) => let ret : Maybe (Fin n) = (Just (natToFinLT i)) in
-- 					let i : Nat = (S i) in
-- 						(search_rec0 n ls x i ret)
