import Data.List

search : (ls : List Nat) -> (n : Nat) -> (x : Nat) -> Nat
search ls n x = 
	let i : Nat = 0 in
		let ret : Nat = n in
			(search_rec0 i ls n ret x)
where 
	search_rec0 : (i : Nat) -> (ls : List Nat) -> (n : Nat) -> (ret : Nat) -> (x : Nat) -> Nat
	search_rec0 i ls n ret x = 
		if not (i < n) then 
			ret
		else 
			if ((index i ls) == x) then 
				let ret : Nat = i in
					let i : Nat = (i + 1) in
						(search_rec0 i ls n ret x)
			else 
				let ret : Nat = ret in
					let i : Nat = (i + 1) in
						(search_rec0 i ls n ret x)

