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
	Lam : (x : String) -> (e : Expr d) -> Expr Write
	Val : (i : Int) -> Expr d
	Proc : (x : String) -> Expr Read


{d : Dir} -> DecEq (Expr d) where 
	decEq (Lam x1 e1) (Lam x2 e2) with (decEq x1 x2)
		decEq (Lam x1 e1) (Lam x1 e2) | Yes Refl  with (decEq e1 e2)
			decEq (Lam x1 e1) (Lam x1 e1) | Yes Refl | Yes Refl  = Yes Refl
			decEq (Lam x1 e1) (Lam x1 e2) | Yes Refl | No prf  = No (\h => prf (case h of
				Refl => Refl))
		decEq (Lam x1 e1) (Lam x2 e2) | No prf  = No (\h => prf (case h of
			Refl => Refl))
	decEq (Lam x1 e1) (Val i2) = No (\h => case h of Refl impossible)
	decEq (Val i1) (Lam x2 e2) = No (\h => case h of Refl impossible)
	decEq (Val i1) (Val i2) with (decEq i1 i2)
		decEq (Val i1) (Val i1) | Yes Refl  = Yes Refl
		decEq (Val i1) (Val i2) | No prf  = No (\h => prf (case h of
			Refl => Refl))
	decEq (Val i1) (Proc x2) = No (\h => case h of Refl impossible)
	decEq (Proc x1) (Val i2) = No (\h => case h of Refl impossible)
	decEq (Proc x1) (Proc x2) with (decEq x1 x2)
		decEq (Proc x1) (Proc x1) | Yes Refl  = Yes Refl
		decEq (Proc x1) (Proc x2) | No prf  = No (\h => prf (case h of
			Refl => Refl))

add5 : (x : Nat) -> Nat
add5 x = 
	let x = x + 5 in
		x

test : Void
test = 
	()

append : {n : Nat} -> {m : Nat} -> {t : Type} -> (v1 : Vect t n) -> (v2 : Vect t m) -> Vect t (n + m)
append n m t v1 v2 = 
	case (v1,v2) of
		(Nil,v2) => v2
		(Cons x xs,v2) => let v3 = append xs v2 in
			Cons x v3

index : (i : Fin n) -> (v : Vect n Nat) -> Nat
index i v = 
	case (i,v) of
		(FZ,Cons t ts) => t
		(FS k,Cons t ts) => index k ts

search : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> Maybe (Fin n)
search n ls x = 
	let i : Nat = 0 in
		let ret : Maybe (Fin n) = Nothing in
			search_rec0 n ls x i ret
where 
	search_rec0 : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> (i : Nat) -> (ret : Maybe (Fin n)) -> Maybe (Fin n)
	search_rec0 n ls x i ret = 
		case isLT i n of
			Yes Refl => case decEq (index (natToFinLT i) ls) x of
				Yes Refl => let ret : Maybe (Fin n) = Just (natToFinLT i) in
					let i : Nat = S i in
						search_rec0 n ls x i ret
				No noprf => let i : Nat = S i in
					search_rec0 n ls x i ret
			No noprf => ret

replicate : {t : Type} -> (x : t) -> (n : Nat) -> Vect t n
replicate t x n = 
	case n of
		0 => Nil
		S n => Cons x (replicate x n)

testLoop : (n : Nat) -> Nat
testLoop n = 
	let x : Nat = 11 in
		let x : Nat = 12 in
			if x < 10 then 
				testLoop_rec0 n x
			else 
				let n = n + 2 in
					n + 4
where 
	testLoop_rec0 : (n : Nat) -> (x : Nat) -> Nat
	testLoop_rec0 n x = 
		if n < 10 then 
			let x : Nat = x + 1 in
				let n = n + 4 in
					testLoop_rec0 n x
		else 
			let n = n + 1 in
				n

test2Loops : (n : Nat) -> Nat
test2Loops n = 
	let x : Nat = 11 in
		test2Loops_rec0 n x
where 
	test2Loops_rec0 : (n : Nat) -> (x : Nat) -> Nat
	test2Loops_rec0 n x = 
		if n < x then 
			let n = n + 1 in
				test2Loops_rec0 n x
		else 
			let y : Nat = 12 in
				test2Loops_rec0 n x y
		test2Loops_rec0 : (n : Nat) -> (x : Nat) -> (y : Nat) -> Nat
		test2Loops_rec0 n x y = 
			if n < 20 then 
				let n = n + 1 in
					test2Loops_rec0 n x y
			else 
				n

testNestedLoops : (n : Nat) -> Nat
testNestedLoops n = 
	let x : Nat = 11 in
		testNestedLoops_rec0 n x
where 
	testNestedLoops_rec0 : (n : Nat) -> (x : Nat) -> Nat
	testNestedLoops_rec0 n x = 
		if n < x then 
			let n = n + 1 in
				let n = n + 3 in
					let m : Nat = n in
						testNestedLoops_rec0 n m x
		else 
			n
		testNestedLoops_rec0 : (n : Nat) -> (m : Nat) -> (x : Nat) -> Nat
		testNestedLoops_rec0 n m x = 
			if m < x then 
				let m : Nat = m + 1 in
					testNestedLoops_rec0 n m x
			else 
				testNestedLoops_rec0 n x

isPrime : (n : Nat) -> Bool
isPrime n = 
	let i : Nat = 2 in
		isPrime_rec0 n i
where 
	isPrime_rec0 : (n : Nat) -> (i : Nat) -> Bool
	isPrime_rec0 n i = 
		if i < n then 
			if 0 < n then 
				let i : Nat = i + 1 in
					let i : Nat = i + 1 in
						isPrime_rec0 n i
			else 
				let i : Nat = i + 2 in
					let i : Nat = i + 1 in
						isPrime_rec0 n i
		else 
			case n of
				0 => let i : Nat = i + 3 in
					True
				n => let i : Nat = i + 6 in
					True

binSearch : (key : Nat) -> (v : Vect Nat n) -> Nat
binSearch key v = 
	let low : Nat = 0 in
		let high : Nat = n - 1 in
			let mid : Nat = 0 in
				let x : Nat = 0 in
					binSearch_rec0 key v high low mid x
where 
	binSearch_rec0 : (key : Nat) -> (v : Vect Nat n) -> (high : Nat) -> (low : Nat) -> (mid : Nat) -> (x : Nat) -> Nat
	binSearch_rec0 key v high low mid x = 
		if low < high + 1 then 
			let mid : Nat = (low + high) / 2 in
				let x : Nat = index v mid in
					if key == x then 
						binSearch_rec0 key v high low mid x
					else 
						if key < x then 
							let high : Nat = mid - 1 in
								let mid : Nat = 0 in
									binSearch_rec0 key v high low mid x
						else 
							let low : Nat = mid + 1 in
								let mid : Nat = 0 in
									binSearch_rec0 key v high low mid x
		else 
			mid

search : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> Maybe (Fin n)
search n ls x = 
	let i : Nat = 0 in
		let ret : Maybe (Fin n) = Nothing in
			search_rec0 n ls x i ret
where 
	search_rec0 : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> (i : Nat) -> (ret : Maybe (Fin n)) -> Maybe (Fin n)
	search_rec0 n ls x i ret = 
		case isLT i n of
			Yes Refl => case decEq (index (natToFinLT i) ls) x of
				Yes Refl => let ret : Maybe (Fin n) = Just (natToFinLT i) in
					let i : Nat = S i in
						search_rec0 n ls x i ret
				No noprf => let i : Nat = S i in
					search_rec0 n ls x i ret
			No noprf => ret

