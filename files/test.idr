isPrime : (n : Nat) -> Bool
isPrime n = 
	let i : Nat = 2 in
		(isPrime_rec0 i n)
where 
	isPrime_rec0 : (i : Nat) -> (n : Nat) -> Bool
	isPrime_rec0 i n = 
		if not (i < n) then 
			case (n) of
				(0) => let i : Nat = (i + 6) in
					True
				(2) => let i : Nat = (i + 6) in
					True
		else 
			if n then 
				let i : Nat = (i + 1) in
					let i : Nat = (i + 1) in
						(isPrime_rec0 i n)
			else 
				let i : Nat = (i + 2) in
					let i : Nat = (i + 1) in
						(isPrime_rec0 i n)

