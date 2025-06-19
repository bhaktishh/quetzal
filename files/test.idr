testLoop : (n : Bool) -> Nat
testLoop n = 
	(testLoop_rec n)
where 
	testLoop_rec : (n : Bool) -> Nat
	testLoop_rec n = 
		if not n then 
			1
		else 
			let n : Bool = True in
				let n : Bool = False in
					(testLoop_rec n)
