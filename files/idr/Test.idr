module Test

testLoop : (n : Nat) -> Nat
testLoop n = 
	let x : Nat = 11 in
		(testLoop_rec n x)
where 
	testLoop_rec : (n : Nat) -> (x : Nat) -> Nat
	testLoop_rec n x = 
		if not (n < 10) then 
			let n : Nat = (n + 1) in
				(n + x)
		else 
			let n : Nat = (n + 4) in
				(testLoop_rec n x)



