import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Defs
import Mathlib.Tactic.Basic

open List Nat

-- DEFINITION 1. ....................................................................
-- Define the set of primes and their additive inverses
def primes_and_inverses : List ℤ :=
  (List.range 100).filter Nat.Prime |>.map (λ p => [↑p, -↑p]) |> List.join

-- Construct the Cayley table T for a finite portion
def cayley_table (n : ℕ) : List (List ℤ) :=
  let primes := (List.range n).filter Nat.Prime |>.map (λ p => ↑p)
  let inverses := primes.map (λ p => -p)
  let first_row := primes
  let first_column := inverses
  let table := first_column.map (λ inv => first_row.map (λ p => p + inv))
  first_row :: table

-- Example of using the cayley_table with a finite portion
def T : List (List ℤ) := cayley_table 30

#eval T -- To visualize a portion of the table

-- DEFINITION 2. ....................................................................
-- Define a sub-array TTi of T, where v x w are its dimensions
def sub_array (T : List (List ℤ)) (r c v w : ℕ) : List (List ℤ) :=
  (T.drop r).take v |>.map (λ row => (row.drop c).take w)

-- Example: Extract a 3x3 sub-array from T
def TT1 : List (List ℤ) := sub_array T 1 1 3 3

#eval TT1 -- Visualize the sub-array

-- DEFINITION 3. ....................................................................
-- Define the structure for the 4-tuple β
structure Beta where
  A : ℤ
  B : ℤ
  L : ℤ
  E : ℤ

-- Create a 4-tuple β from the vertices of a sub-array TTi
def create_beta (TTi : List (List ℤ)) : Beta :=
  ⟨TTi.head!.head!, TTi.head!.getLast!, TTi.getLast!.head!, TTi.getLast!.getLast!⟩

-- Example usage: Create β for TT1
def β1 : Beta := create_beta TT1

#eval β1.A -- Visualize β1
#eval β1.B -- Visualize β1
#eval β1.L -- Visualize β1
#eval β1.E -- Visualize β1

-- LEMMA 4.1. .......................................................................

lemma lemma_4_1 (m n c k : ℤ) :
  let TTi_A := m + n
  let TTi_B := m + (n + k)
  let TTi_L := (m + c) + n
  let TTi_E := (m + c) + (n + k)
  TTi_B + TTi_L = TTi_A + TTi_E :=
by
   linarith

-- LEMMA 4.2. .......................................................................

-- LEMMA 4.3. .......................................................................

-- LEMMA 4.4. .......................................................................

-- LEMMA 4.5. .......................................................................

-- THEOREM 1. .......................................................................

-- THEOREM 2. .......................................................................
