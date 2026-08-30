module Main 

import Data.Vect
import Data.Fin 
import Decidable.Equality

Matrix : Nat -> Nat -> Type
Matrix m n = Vect m (Vect n Nat)

index : Matrix m n -> Fin m -> Fin n -> Nat
index [] _ _ impossible 
index (x :: xs) FZ j = Vect.index j x
index (x :: xs) (FS y) j = index xs y j 

zeros : (m : Nat) -> (n : Nat) -> Matrix m n 
zeros m n = replicate m (replicate n 0)

updateAt : Matrix m n -> Fin m -> Fin n -> (Nat -> Nat) -> Matrix m n 
updateAt mtrx i j f = Vect.updateAt i (Vect.updateAt j f) mtrx

update : Matrix m n -> Fin m -> Fin n -> Nat -> Matrix m n 
update mtrx i j x = updateAt mtrx i j (const x)

transpose : {m : Nat} -> {n : Nat} -> Matrix m n -> Matrix n m 
transpose x =

-- transpose : {m : Nat} -> {n : Nat} -> (x : Matrix m n) -> Matrix n m
-- transpose {m} {n} x = 
-- 	let tx : Matrix n m = zeros n m in
-- 		let i : Nat = 0 in
-- 			let j : Nat = 0 in
-- 				transpose_rec0 {m} {n} x i j tx
-- where 
-- 	transpose_rec0 : {m : Nat} -> {n : Nat} -> (x : Matrix m n) -> (i : Nat) -> (j : Nat) -> (tx : Matrix n m) -> Matrix n m
-- 	transpose_rec0 {m} {n} x i j tx = 
-- 		case isLT i n of
-- 			Yes yesprf => transpose_rec1 {m} {n} x i j tx
-- 			No noprf => tx
-- where 
--     transpose_rec1 : {m : Nat} -> {n : Nat} -> (x : Matrix m n) -> (i : Nat) -> (j : Nat) -> (tx : Matrix n m) -> Matrix n m
--     transpose_rec1 {m} {n} x i j tx = 
--         case isLT j m of
--             Yes yesprf => 
--                 let tx = update tx ?fwe ?wefwe (index x ?wefw ?ewfw) in
--                 let i : Nat = i + 1 in
--                     transpose_rec1 {m} {n} x i j tx
--             No noprf => let j : Nat = j + 1 in
--                 transpose_rec0 {m} {n} x i j tx
