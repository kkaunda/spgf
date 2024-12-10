import Mathlib
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Defs
import Mathlib.Tactic.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.ModCases
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.ModEq

open List Nat

-- Define a finite portion of a Cayley table.
def cayley_table (n : ℕ) : List (List ℤ) :=
  let primes := (List.range n).filter Nat.Prime |>.map (λ p => ↑p)
  let inverses := primes.map (λ p => -p)
  let first_row := 0 :: primes
  let table := inverses.map (λ inv => inv :: (primes.map (λ p => p + inv)))
  first_row :: table

-- Function to create a valid sub-array from a Cayley table.
def sub_array (n start_c end_c end_r : ℕ) : Option (List (List ℤ)) :=
  let table := cayley_table n
  let fixed_r := 2
  if start_c < 3 ∨ end_c < start_c ∨ end_r < fixed_r + 2 ∨ end_r > table.length ∨ end_c > (table.head?.getD []).length then
    none
  else
    some ((table.drop fixed_r).take (end_r - fixed_r + 1)
      |>.map (λ row => (row.drop start_c).take (end_c - start_c + 1)))

-- Define Beta structure.
structure Beta where
  A : ℤ
  B : ℤ
  L : ℤ
  E : ℤ
  isValid : A < B ∧ A > L ∧ B > L ∧ B > E ∧ L < E ∧ A = E
  deriving Repr

def beta_from_sub_array (sub : Option (List (List ℤ))) : Option Beta :=
  match sub with
  | none => none
  | some subArray =>
    let A := subArray.head?.bind (λ row => row.head?)
    let B := subArray.head?.bind (λ row => row.getLast?)
    let L := subArray.getLast?.bind (λ row => row.head?)
    let E := subArray.getLast?.bind (λ row => row.getLast?)
    match (A, B, L, E) with
    | (some a, some b, some l, some e) =>
      if h : a < b ∧ a > l ∧ b > l ∧ b > e ∧ l < e ∧ a = e then
        some { A := a, B := b, L := l, E := e, isValid := h }
      else none
    | _ => none

-- lemma 4.1
-- an important result especially for a combinatorial proof
lemma beta_field_sum_from_cayley (β : Beta) (m n c k : ℤ)
  (hA : β.A = m + n)
  (hB : β.B = m + (n + k))
  (hL : β.L = (m + c) + n)
  (hE : β.E = (m + c) + (n + k)) :
  β.B + β.L = β.A + β.E := by
  -- Substitute the relationships for β.A, β.B, β.L, and β.E.
  rw [hA, hB, hL, hE]
  -- Simplify the resulting equation.
  linarith

-- lemma 4.2
-- Theorem to prove that all primes > 3 can be expressed
-- in the form 6n ± 1.
theorem prime_form_6n_plus_1_or_6n_minus_1 (p : ℕ) (hprime : Nat.Prime p) (hp : 3 < p) :
    ∃ n, (p = 6 * n + 1 ∨ p = 6 * n - 1) := by
  suffices p % 6 = 1 ∨ p % 6 = 5 by
    obtain hp | hp := this
    · use p / 6
      left
      omega
    · use (p / 6 + 1)
      right
      omega
  have : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have : p ≠ 2 := by linarith
  have : p ≠ 3 := by linarith
  have : p ≠ 6 := by rintro rfl; norm_num at hprime
  interval_cases hr : p % 6 <;> first | omega | (exfalso; revert hr)
  · rw [← Nat.dvd_iff_mod_eq_zero, Nat.dvd_prime hprime]
    aesop
  · refine ne_of_apply_ne (· % 2) ?_
    dsimp
    rw [Nat.mod_mod_of_dvd _ (by norm_num), ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_prime hprime]
    aesop
  · refine ne_of_apply_ne (· % 3) ?_
    dsimp
    rw [Nat.mod_mod_of_dvd _ (by norm_num), ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_prime hprime]
    aesop
  · refine ne_of_apply_ne (· % 2) ?_
    dsimp
    rw [Nat.mod_mod_of_dvd _ (by norm_num), ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_prime hprime]
    aesop

-- Lemma 4.3, 4.4, and 4.5.
theorem infinitely_many_betas_with_prime_properties (p : ℕ) (hprime : Nat.Prime p) (hmin : 3 < p) :
  Set.Infinite {β : Beta |
    ∃ x y : ℤ,
      x < x + y ∧
      y > 0 ∧
      (
        (↑p = 6 * (x + y) - 1 ∧
          β.A = 6 * x + 6 * y - 4 ∧ β.B = 6 * x + 12 * y - 8 ∧ β.L = 6 * x ∧ β.E = 6 * x + 6 * y - 4 ∧
          Nat.Prime (β.B + 3).toNat ∧ Nat.Prime ((β.B + 3) - β.E).toNat
        ) ∨
        (↑p = 6 * (x + y) + 1 ∧
          β.A = 6 * x + 6 * y - 2 ∧ β.B = 6 * x + 12 * y - 4 ∧ β.L = 6 * x ∧ β.E = 6 * x + 6 * y - 2 ∧
          Nat.Prime (β.B + 3).toNat ∧ Nat.Prime ((β.B + 3) - β.E).toNat
        )
      )
  } :=
by sorry

