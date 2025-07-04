import Decidable.Equality

data MyPair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
	MkMyPair : (x : a) -> (pf : p x) -> MyPair a p

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

(DecEq t) => DecEq (MyVect n t) where 
	decEq MyNil MyNil = Yes Refl 
	decEq (MyCons h1 t1) (MyCons h2 t2) with (decEq h1 h2)
		decEq (MyCons h1 t1) (MyCons h1 t2) | Yes Refl with (decEq t1 t2) 
			decEq (MyCons h1 t1) (MyCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
			decEq (MyCons h1 t1) (MyCons h1 t2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
		decEq (MyCons h1 t1) (MyCons h2 t2) | No prf = No $ (\h => prf (case h of Refl => Refl))

data MyList : (t : Type) -> Type where
	MyListNil : MyList t
	MyListCons : (head : t) -> (tail : MyList t) -> MyList t

(DecEq t) => DecEq (MyList t) where
	decEq MyListNil MyListNil = Yes Refl 
	decEq (MyListCons h1 t1) (MyListCons h2 t2) with (decEq h1 h2)
		decEq (MyListCons h1 t1) (MyListCons h1 t2) | Yes Refl with (decEq t1 t2)
			decEq (MyListCons h1 t1) (MyListCons h1 t1) | Yes Refl | Yes Refl = Yes Refl 
			decEq (MyListCons h1 t1) (MyListCons h1 t2) | Yes Refl | No prf = No $ (\h => prf (case h of Refl => Refl))
		decEq (MyListCons h1 t1) (MyListCons h2 t2) | No prf = No $ (\h => prf (case h of Refl => Refl))
	decEq MyListNil (MyListCons h t) = No (\h => (case h of Refl impossible ))
	decEq (MyListCons h t) MyListNil = No (\h => (case h of Refl impossible ))

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
