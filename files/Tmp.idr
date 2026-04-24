import Decidable.Equality
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

