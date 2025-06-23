test2Loops : (n : Nat) -> Nat
test2Loops n = 
	let x : Nat = 11 in
		(test2Loops_rec0 n x)
where 
	test2Loops_rec0 : (n : Nat) -> (x : Nat) -> Nat
	test2Loops_rec0 n x = 
		if not (n < x) then 
			let y : Nat = 12 in
				(test2Loops_rec0_rec0 n x y)
		else 
			let n = (n + 1) in
				(test2Loops_rec0 n x)
 where 
		test2Loops_rec0_rec0 : (n : Nat) -> (x : Nat) -> (y : Nat) -> Nat
		test2Loops_rec0_rec0 n x y = 
			if not (n < 20) then 
				n
			else 
				let n = (n + 1) in
					(test2Loops_rec0_rec0 n x y)

