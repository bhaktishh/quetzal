test : (n : Nat) -> Nat
test n = 
	(case (n,n) of
		(0,0) => n
		(_,_) => let n : Nat = 0 in
			n)

