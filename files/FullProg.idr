import Decidable.Equality
import Decidable.Equality
import Data.Nat
import Data.Vect
import Data.Nat
import Decidable.Equality
data Vect : (n : Nat) -> (t : Type) -> Type where 
	Nil : Vect 0 t
	Cons : (head : t) -> (tail : Vect n t) -> Vect (S n) t


{n : Nat} -> {t : Type} -> DecEq t => DecEq (Vect n t) where 
	decEq Nil Nil = Yes Refl
	decEq (Cons head1 tail1) (Cons head2 tail2) with (decEq head1 head2)
		decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl  with (decEq tail1 tail2)
			decEq (Cons head1 tail1) (Cons head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (Cons head1 tail1) (Cons head2 tail2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

data Test : (a : Type) -> (z : Type) -> (p : (z : Type) -> (a : x) -> Type) -> Type where 
	MkTest : (x : a) -> (z : Type) -> (pf : p z x) -> Test a z p


{a : Type} -> {z : Type} -> {p : (z : Type) -> (a : x) -> Type} -> DecEq a => DecEq z => (z : Type) -> (a : x) -> DecEq (p z a) => DecEq (Test a z p) where 
	decEq (MkTest x1 z pf1) (MkTest x2 z pf2) with (decEq x1 x2)
		decEq (MkTest x1 z pf1) (MkTest x1 z pf2) | Yes Refl  with (decEq pf1 pf2)
			decEq (MkTest x1 z pf1) (MkTest x1 z pf1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MkTest x1 z pf1) (MkTest x1 z pf2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (MkTest x1 z pf1) (MkTest x2 z pf2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

data MyPair : (a : Type) -> (p : (x : a) -> Type) -> Type where 
	MkMyPair : (x : a) -> (y : p x) -> MyPair a p


{a : Type} -> {p : (x : a) -> Type} -> DecEq a => (x : a) -> DecEq (p x) => DecEq (MyPair a p) where 
	decEq (MkMyPair x1 y1) (MkMyPair x2 y2) with (decEq x1 x2)
		decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl  with (decEq y1 y2)
			decEq (MkMyPair x1 y1) (MkMyPair x1 y1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MkMyPair x1 y1) (MkMyPair x1 y2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (MkMyPair x1 y1) (MkMyPair x2 y2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

data MyCurse : (a : Type) -> (b : (x : a) -> Type) -> (p : (x : a) -> (y : b x) -> Type) -> Type where 
	MkMyCurse : {a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : b x) -> Type} -> (x : a) -> (y : b x) -> (pf : p x y) -> MyCurse a b p


{a : Type} -> {b : (x : a) -> Type} -> {p : (x : a) -> (y : b x) -> Type} -> DecEq a => (x : a) -> DecEq (b x) => (x : a) -> (y : b x) -> DecEq (p x y) => DecEq (MyCurse a b p) where 
	decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) with (decEq x1 x2)
		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl  with (decEq y1 y2)
			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl  with (decEq pf1 pf2)
				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf1) | Yes Refl | Yes Refl | Yes Refl  = Yes Refl
				decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y1 pf2) | Yes Refl | Yes Refl | No prf  = No (\h => prf (case h of
					Refl => Refl))
			decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x1 y2 pf2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (MkMyCurse x1 y1 pf1) (MkMyCurse x2 y2 pf2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

data MyEither : (a : Type) -> (b : Type) -> Type where 
	MyLeft : (x : a) -> MyEither a b
	MyRight : (y : b) -> MyEither a b


{a : Type} -> {b : Type} -> DecEq a => DecEq b => DecEq (MyEither a b) where 
	decEq (MyLeft x1) (MyLeft x2) with (decEq x1 x2)
		decEq (MyLeft x1) (MyLeft x1) | Yes Refl  = Yes Refl
		decEq (MyLeft x1) (MyLeft x2) | No prf  = No (\h => prf (case h of
			Refl => Refl))
	decEq (MyLeft x1) (MyRight y2) = No (\h => case h of Refl impossible)
	decEq (MyRight y1) (MyLeft x2) = No (\h => case h of Refl impossible)
	decEq (MyRight y1) (MyRight y2) with (decEq y1 y2)
		decEq (MyRight y1) (MyRight y1) | Yes Refl  = Yes Refl
		decEq (MyRight y1) (MyRight y2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

data Test : (s : Bool) -> Type where 
	C1 : (s : Bool) -> Test s


{s : Bool} -> DecEq (Test s) where 
	decEq (C1 s) (C1 s) = Yes Refl

data Test : (t : Type) -> Type where 
	C1 : (s : Bool) -> Test t


{t : Type} -> DecEq t => DecEq (Test t) where 
	decEq (C1 s1) (C1 s2) with (decEq s1 s2)
		decEq (C1 s1) (C1 s1) | Yes Refl  = Yes Refl
		decEq (C1 s1) (C1 s2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

record DPairRec (t : Type) (p : (a : t) -> Type) where 
	constructor MkDPairRec
	fst : t
	snd : p fst


{t : Type} -> {p : (a : t) -> Type} -> DecEq t => (a : t) -> DecEq (p a) => DecEq (DPairRec t p) where 
	decEq (MkDPairRec fst1 snd1) (MkDPairRec fst2 snd2) with (decEq fst1 fst2)
		decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd2) | Yes Refl  with (decEq snd1 snd2)
			decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (MkDPairRec fst1 snd1) (MkDPairRec fst1 snd2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (MkDPairRec fst1 snd1) (MkDPairRec fst2 snd2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

data Vect : (n : Nat) -> (t : Type) -> Type where 
	Nil : Vect 0 t
	Cons : (head : t) -> (tail : Vect n t) -> Vect (S n) t


{n : Nat} -> {t : Type} -> DecEq t => DecEq (Vect n t) where 
	decEq Nil Nil = Yes Refl
	decEq (Cons head1 tail1) (Cons head2 tail2) with (decEq head1 head2)
		decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl  with (decEq tail1 tail2)
			decEq (Cons head1 tail1) (Cons head1 tail1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (Cons head1 tail1) (Cons head1 tail2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (Cons head1 tail1) (Cons head2 tail2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

data Dir : Type where 
	Write : Dir
	Read : Dir


DecEq Dir where 
	decEq Write Write = Yes Refl
	decEq Write Read = No (\h => case h of Refl impossible)
	decEq Read Write = No (\h => case h of Refl impossible)
	decEq Read Read = Yes Refl

data Expr : (d : Dir) -> Type where 
	Lam : (x : String) -> (e : Expr d) -> E


	