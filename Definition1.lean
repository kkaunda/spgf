def hi := "Hi!"
/- krk
import Mathlib.Data.Nat.Prime.Basic
import data.list.basic
import tactic

open list

-- Function to return the first n prime numbers, but conceptually primes are infinite
def first_n_primes (n : ℕ) : list ℕ :=
(list.filter nat.prime (list.range (n * 20))).take n

-- Function to calculate the additive inverse of each prime
def additive_inverses (primes : list ℕ) : list ℤ :=
primes.map (λ p, -(p : ℤ))

-- Function to construct the Cayley table
def cayley_table (n : ℕ) : list (list ℤ) :=
let primes := first_n_primes n in
let inverses := additive_inverses primes in
let first_row := primes.map (λ p, p : ℤ) in
let first_column := inverses in
(let rest_of_table := (list.range n).map (λ i,
   (list.range n).map (λ j,
     first_row.nth_le j (by simp) + first_column.nth_le i (by simp))
   ) in
 first_row :: rest_of_table.map (λ row, 0 :: row))

-- Define an instance of the Cayley table, which we can refer to as T
def T : list (list ℤ) := cayley_table 10  -- Generates a 10x10 portion of the infinite Cayley table

-- Example of extracting the Cayley table
#eval T
-/
