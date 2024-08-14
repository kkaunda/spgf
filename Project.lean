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

-- Lemma 4.2: All Primes Greater Than 3 are of the Form 6n ± 1
-- This lemma is a well-known result in number theory.

-- lean 4 code here


-- LEMMA 4.3. .......................................................................
-- Let TTi be a term in T where the indexes m, n >=0 and refer to the rows and columns in T
-- respectively.
-- Prove that for every prime pα ≥ 5, there exists a sub-array TTi ∈ T such that the following
-- properties are simultaneously true:
-- Property 1 : TTi.A + 3 ∈ {6n ± 1 | n ∈ ℕ}
-- Property 2 : (TTi.B + 3) - TTi.E ∈ {6n ± 1 | n ∈ ℕ}
-- Property 3 : TTi.L ≡ 0 (mod 6)
-- Property 4 : TTi.A = TTi.E
-- Property 5 : TTi.B + 3 ∈ {6n ± 1 | n ∈ ℕ}
-- If and only if
-- for TTi.A + 3 ∈ {6n - 1 | n ∈ ℕ}
-- TTi.A = 6x + 6y - 4
-- TTi.B = 6x + 12y - 8
-- TTi.L = 6x
-- TTi.E = 6x + 6y - 4
-- for TTi.A + 3 ∈ {6n + 1 | n ∈ ℕ}
-- TTi.A = 6x + 6y - 2
-- TTi.B = 6x + 12y - 4
-- TTi.L = 6x
-- TTi.E = 6x + 6y - 2
-- where n ∈ ℕ, x < n, y > 0, n = x + y, (TTi.A + 3) = pα and TTi.A = t2,k.
--
-- Notes
-- This result demonstrates the existence of a pattern. It algebraically shows that for every
-- prime pα ≥ 5, there is a pattern TTi that defines a pair of integers Qi and Ri such that
-- Ri − Qi = pα − 3.
-- The key in the proof of this result is the following analysis:
-- •	We are given pα as a constant quantity.
-- •	Now pα can be expressed in the form 6n ± 1.
-- •	This implies that n in the expression 6n ± 1 is constant.
-- •	We then let n = x + y.
-- •	We then use combinatory analysis to heuristically determine which expressions to assign to
-- A, B, L and E from the sets M = (6x, 6y, -4, 6x, 6y, -4) and N = (6x, 6y, -2, 6x, 6y, -2) such
--  that the five (5) properties of Lemma 4.3 are satisfied.
-- But how are the sets M and N derived?
-- Notice that by Lemma 4.3, TTi.A = TTi.E and (TTi.A + 3) = pα. Since pα is prime then it can be
-- expressed in the forms 6n ± 1 or 6(x + y) ± 1. And by Lemma 4.1, A + E  = B  + L, which implies
--  that TTi.B  + TTi.L  = TTi.A + TTi.E = ((6x + 6y + -4) + (6x + 6y + -4)) or
-- ((6x + 6y + -2) + (6x + 6y + -2)) depending on which form pα can be expressed.

-- lean 4 code here


-- LEMMA 4.4. .......................................................................
-- Lemma 4.4
-- Let any sub-array TTi that satisfies Lemma 4.3 be referred to as a Prime Array.
-- Prove that for every prime pα ≥ 5, there are infinitely many Prime Arrays
-- such that TTi.A = pα - 3.
-- Notes
-- This will show that for any prime pα ≥ 5 the pattern defined by the Prime Array TTi occurs
-- infinitely often and that consequently, the integer pairs (Qi, Ri) also occur infinitely often.
-- The key in the proof is to show that for any prime pα ≥ 5,
-- •	pα is constant.
-- •	Which implies n is constant.
-- •	But n = x + y
-- •	Now changing the value of  y changes the value of x in order to maintain the
--    equality n = x + y.
-- •	Changing the value of x changes the value of L since L = 6x.
-- •	Changing the value of L changes the value of B since B + L = A + E and A + E is a constant
--    expression.
-- •	This implies that the value of y can be changed infinitely often and each change represents
--    a different sub-array or Prime Array TTi.

-- lean 4 code here



-- LEMMA 4.5. .......................................................................
-- Lemma 4.5: Prove that: For every prime pα ≥ 5, there exists infinitely many Prime Arrays, TTi,
-- such that TTi .A = pα − 3 and (Ti.B + 3) and ((Ti.B + 3) −Ti.E) are prime.
-- Notes
-- This will show that for any prime pα ≥ 5, the Prime Arrays TTi occur infinitely often and
-- Qi and Ri are prime. Notice that here, (TTi.B + 3) = Ri and Qi = ((TTi.B + 3) − TTi.E).
-- The proof here relies on the construction of T where all the elements on the first row of T
-- are prime
-- We can then algebraically show that (TTi.B + 3) and ((TTi.B + 3) − TTi.E) are prime.

-- lean 4 code here



-- THEOREM 1. .......................................................................
-- Theorem 1:	Prove that: For every prime pα, there exists infinitely many pairs of primes,
-- (pn, pn+m), such that (pn+m − pn) = pα − 3, where n, α ≥ 3, m ≥ 1, and pn is the nth prime.
-- Notes
-- The claim is that this result is implied from the previous results as demonstrated in the
-- following steps:
-- Step 1: By Lemma 4.5, and the construction of T, TTi.A and TTi.E are prime gaps.
-- Step 2: By Lemma 4.3, TTi.A = TTi.E.
-- This is equivalent to: (TTi.A + 3) − 3  = ((TTi.B + 3) − ((TTi.B + 3) − TTi.E)).
-- Step 3: By Lemma 4.5, the following are prime; (TTi.A + 3), ((TTi.B + 3) − TTi.E), (TTi.B + 3).
-- Step 4: By Lemma 4.5, for every prime (TTi.A + 3) ≥ 5, there are infinitely many of the
-- following pairs of primes defined as: (((TTi.B + 3) − TTi.E), (TTi.B + 3)).
-- We can then see that the following statement is implied:
-- For every prime (TTi.A + 3) ≥ 5, there exists infinitely many pairs of primes,
-- (((TTi.B + 3) − TTi.E), (TTi.B + 3)), such that ((TTi.B + 3) − ((TTi.B + 3) − TTi.E)) =
-- (TTi.A + 3) − 3.
-- This statement is equivalent to the formal statement of Theorem 1 which can be is re-stated
-- using the following equivalent assignments:
-- pα − 3 = TTi.A.
-- pn+m − 3 = TTi.B.
-- pα − pn = TTi.L.
-- pn+m − pn = TTi.E.

-- lean 4 code here



-- THEOREM 2. .......................................................................
-- Theorem 2: Prove that there exist infinitely many pairs of primes with a gap of 2.
-- Notes
-- This result is just a special case of Theorem 1 when pα is set to 5. I am sure this would be
-- resolved by LEAN4 using the "refl" similar tactic.

-- lean 4 code here


-- END
