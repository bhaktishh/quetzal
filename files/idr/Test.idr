module Test

	g : (x : Int) -> (p : x = 5) -> ()
	g x p = () 

	f : () 
	f = let x : Int
	        x = 5 in
			let p : (x = 5) = Refl in
				let x = x + 1 in 
						g x p
