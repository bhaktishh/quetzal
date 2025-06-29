import Data.Vect

import Data.Nat

import Decidable.Equality

search : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> Maybe (Fin n)
search n ls x = 
	let i : Nat = 0 in
		let ret : Maybe (Fin n) = Nothing in
			(search_rec0 n ls x i ret)
where 
	search_rec0 : (n : Nat) -> (ls : Vect n Nat) -> (x : Nat) -> (i : Nat) -> (ret : Maybe (Fin n)) -> Maybe (Fin n)
	search_rec0 n ls x i ret = 
		case ((isLT i n)) of
			(No noprf) => ret
			(Yes yesprf) => case ((decEq (index (natToFinLT i) ls) x)) of
				(No noprf) => let i : Nat = (S i) in
					(search_rec0 n ls x i ret)
				(Yes yesprf) => let ret : Maybe (Fin n) = (Just (natToFinLT i)) in
					let i : Nat = (S i) in
						(search_rec0 n ls x i ret)

