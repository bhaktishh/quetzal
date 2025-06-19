module Test

testLoop : (n : Nat) -> Nat
testLoop n = 
	let x : Nat = 11 in
		(testLoop_rec n)
where 
	testLoop_rec : (n : Nat) -> Nat
	testLoop_rec n = 
		if not (n < 10) then 
			let n : Nat = (n + 1) in
				(n + x)
		else 
			let n : Nat = (n + 4) in
				(testLoop_rec n)

