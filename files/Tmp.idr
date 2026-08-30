import Decidable.Equality
transpose : {m : Nat} -> {n : Nat} -> (x : Matrix m n) -> Matrix n m
transpose {m} {n} x = 
	let tx : Matrix n m = zeros n m in
		let i : Nat = 0 in
			let j : Nat = 0 in
				transpose_rec0 {m} {n} x i j tx
where 
	transpose_rec0 : {m : Nat} -> {n : Nat} -> (x : Matrix m n) -> (i : Nat) -> (j : Nat) -> (tx : Matrix n m) -> Matrix n m
	transpose_rec0 {m} {n} x i j tx = 
		case isLT i n of
			Yes Refl => transpose_rec0 {m} {n} x i j tx
			No noprf => tx
		transpose_rec0 : {m : Nat} -> {n : Nat} -> (x : Matrix m n) -> (i : Nat) -> (j : Nat) -> (tx : Matrix n m) -> Matrix n m
		transpose_rec0 {m} {n} x i j tx = 
			case isLT j m of
				Yes Refl => let tx = update tx (natToFinLT j) (natToFinLT i) (index x (natToFinLT i) (natToFinLT j)) in
					let i : Nat = i + 1 in
						transpose_rec0 {m} {n} x i j tx
				No noprf => let j : Nat = j + 1 in
					transpose_rec0 {m} {n} x i j tx

