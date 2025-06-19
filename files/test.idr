testLoop : (n : Nat) -> Nat
testLoop n = 
	let x : Nat = 11 in
		let testLoop_recVal : Nat = (testLoop_rec n) in
			let n : Nat = (n + 1) in
				n
where 
	testLoop_rec : (n : Nat) -> Nat
	testLoop_rec n = 
		if not (n < 10) then 
			n
		else 
			let n : Nat = (n + 4) in
				(testLoop_rec n)

