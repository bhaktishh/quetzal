search : (n : Nat) -> (v : Vect n Nat) -> (x : Nat) -> Fin n
search n v x = 
	let i : Fin n = 0 in
		let ret : Fin n = n in
			(search_rec0 n v x i ret)
where 
	search_rec0 : (n : Nat) -> (v : Vect n Nat) -> (x : Nat) -> (i : Fin n) -> (ret : Fin n) -> Fin n
	search_rec0 n v x i ret = 
		if not ((finToNat i) < n) then 
			ret
		else 
			if ((index i v) == x) then 
				let ret : Fin n = i in
					let i : Fin n = (i + 1) in
						(search_rec0 n v x i ret)
			else 
				let i : Fin n = (i + 1) in
					(search_rec0 n v x i ret)

