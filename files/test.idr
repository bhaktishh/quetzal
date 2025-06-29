search : (n : Nat) -> (v : Vect n Nat) -> (x : Nat) -> Fin n
search n v x = 
	let i : Fin n = 0 in
		let ret : Nat = n in
			(search_rec0 i n ret v x)
where 
	search_rec0 : (i : Fin n) -> (n : Nat) -> (ret : Nat) -> (v : Vect n Nat) -> (x : Nat) -> Fin n
	search_rec0 i n ret v x = 
		if not (i < n) then 
			ret
		else 
			if ((index i ls) == x) then 
				let ret : Nat = i in
					let i : Fin n = (i + 1) in
						(search_rec0 i n ret v x)
			else 
				let i : Fin n = (i + 1) in
					(search_rec0 i n ret v x)

