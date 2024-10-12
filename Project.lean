import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Dvd
import Mathlib.Algebra.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.ModEq

open Bool Subtype
open Nat List Algebra
namespace Nat



lemma lemma_4_2 (p : ℕ) (hprime : Nat.Prime p) (hpg3 : p > 3)  :
    ∃ n, p = 6 * n + 1 ∨ p = 6 * n - 1 := by

  by_contra! hneg

  mod_cases hp : p % 6
  {
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hp
    have hp : 3 * (2*k) = p := by
      rw [←mul_assoc]
      exact hk.symm
    apply Nat.not_prime_mul' hp
    · norm_num
    · omega
    · exact hprime
  }
  {
    sorry
    --example (p : ℤ) (h0 : p ≡ 2 [PMOD 6]) : p - 2 ≡ 0 [PMOD 6] := AddCommGroup.sub_modEq_zero.mpr h0
  }
  {
    --let (q : ℤ) (hq : q = p)

    have hp' : p - 2 ≡ 0 [MOD 6] := by
      --AddCommGroup.sub_modEq_zero.mpr hp
      sorry







    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hp'
    have hkp : 2 * (3*k + 1) = p := by
      rw [mul_add, ←mul_assoc, mul_one]
      convert hk.symm using 0
      omega
    apply Nat.not_prime_mul' hkp
    · norm_num
    · omega
    · exact hprime
  }
  {
    have hp' : p - 3 ≡ 0 [MOD 6] := by
      sorry
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hp'
    have hkp : 3 * (2*k + 1) = p := by
      rw [mul_add, ←mul_assoc, mul_one]
      convert hk.symm using 0
      omega
    apply Nat.not_prime_mul' hkp
    · norm_num
    · omega
    · exact hprime
  }
  {
    sorry
  }
  {
    sorry
  }
