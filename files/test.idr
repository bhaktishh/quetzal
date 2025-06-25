test2Loops : (n : Nat) -> Nat
test2Loops n = 
	let x : Nat = 11 in
		(test2Loops_rec0 n x)
where 
	test2Loops_rec0 : (n : Nat) -> (x : Nat) -> Nat
	test2Loops_rec0 n x = 
		if not (n < x) then 
			n
		else 
			let n = (n + 1) in
				let n = (n + 3) in
					let m : Nat = n in
						(test2Loops_rec0_rec0 m n x)
 where 
		test2Loops_rec0_rec0 : (m : Nat) -> (n : ?) -> (x : Nat) -> Nat
		test2Loops_rec0_rec0 m n x = 
			if not (m < x) then 
				(test2Loops_rec0 n x)
			else 
				let m = (m + 1) in
					(test2Loops_rec0_rec0 m n x)

