module Test

-- func isPrime (Nat n) of Bool {
--     Nat i = 2;
--     while (i < n) {
--         if (n % i == 0) {
--             if (!(n == i)) {
--                 return False;
--             } else {
--                 ()
--             }
--         } else {
--             ()
--         }
--     }
--     return True;
-- }

isPrime : Nat -> Bool 
isPrime n = let i : Nat = 2 in isPrimeRec n i 
	where
		isPrimeRec : Nat -> Nat -> Bool
		isPrimeRec n i = 
			if (not (i < n)) then 
				True else (if (remainder n i == 0) then True else False)
				-- (if (n % i == 0 && n != i) then 
				-- False else True)
						-- (let i = i + 1 in 
						-- 	isPrimeRec n (i + 1)))