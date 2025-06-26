binSearch : (key : Nat) -> (v : Vect n Nat) -> Fin n
binSearch key v = 
	let low : Fin n = 0 in
		let high : Fin n = (n - 1) in
			let mid : Fin n = 0 in
				let x : Nat = 0 in
					let ret : Fin n = 0 in
						(binSearch_rec0 high key low mid ret v x)
where 
	binSearch_rec0 : (high : Fin n) -> (key : Nat) -> (low : Fin n) -> (mid : Fin n) -> (ret : Fin n) -> (v : Vect n Nat) -> (x : Nat) -> Fin n
	binSearch_rec0 high key low mid ret v x = 
		if not (low < (high + 1)) then 
			ret
		else 
			let mid : Fin n = ((low + high) / 2) in
				let x : Nat = (index mid v) in
					if (key == x) then 
						let ret : Fin n = mid in
							(binSearch_rec0 high key low mid ret v x)
					else 
						if (key < x) then 
							let high : Fin n = (mid - 1) in
								(binSearch_rec0 high key low mid ret v x)
						else 
							let low : Fin n = (mid + 1) in
								(binSearch_rec0 high key low mid ret v x)

