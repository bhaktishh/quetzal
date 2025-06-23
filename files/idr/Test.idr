module Test

testLoop : (n : Nat) -> Nat
testLoop n = 
	let x : Nat = 11 in
		let x : Nat = 12 in
			if (x < 10) then 
				(testLoop_rec n)
			else 
				let n : Nat = (n + 2) in
					(n + 4)
where 
	testLoop_rec : (n : Nat) -> Nat
	testLoop_rec n = 
		if not (n < 10) then 
			let n : Nat = (n + 1) in
				n
		else 
			let n : Nat = (n + 4) in
				(testLoop_rec n)



