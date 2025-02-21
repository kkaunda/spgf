import Mathlib

set_option linter.unusedVariables false

def primes_set := { n | Nat.Prime n }
instance : Infinite primes_set := Nat.infinite_setOf_prime.to_subtype
instance : DecidablePred (fun n => n ∈ primes_set) := fun n => Nat.decidablePrime n

def primes (n : ℕ) : ℕ := if (n = 0) then 0 else Nat.Subtype.ofNat primes_set (n - 1)

lemma primes_zero : primes 0 = 0 := rfl

def primes_inv_exists (n : ℕ) (n_prime : Nat.Prime n) : ∃ i, primes i = n :=
by
  have := Nat.Subtype.ofNat_surjective (s := primes_set)
  obtain ⟨a, ha⟩ := this ⟨n, n_prime⟩
  use a + 1
  simp [primes, ha]

def primes_inv (n : ℕ) (n_prime : Nat.Prime n) : ℕ := Nat.find (primes_inv_exists n n_prime)
def primes_inv_def (n : ℕ) (n_prime : Nat.Prime n) : primes (primes_inv n n_prime) = n :=
Nat.find_spec (primes_inv_exists n n_prime)

lemma primes_inv_pos (n : ℕ) (n_prime : Nat.Prime n) : 0 < primes_inv n n_prime :=
by
  rw [zero_lt_iff]
  intro h
  replace h := congrArg primes h
  rw [primes_inv_def, primes_zero] at h
  exact n_prime.ne_zero h

lemma primes_prime {n : ℕ} (hn : n > 0) : Nat.Prime (primes n) :=
by
  unfold primes
  rw [if_neg hn.ne']
  exact Subtype.mem _

def cayley_table (row col : ℕ) : ℤ := primes col - primes row

-- -------------------------------------------------------

structure Ds where
  y      : ℕ
  y_pos  : y > 0
  width  : ℕ
  height : ℕ

structure Beta where
  d          : Ds
  P          : ℕ
  three_lt_P : 3 < P := by decide
  prime_P    : Nat.Prime P := by decide

-- -------------------------------------------------------
lemma primes_two_eq_three : primes 2 = 3 := by native_decide


def Beta.primeIndex (β : Beta) := primes_inv β.P β.prime_P

def Beta.A (β : Beta) := cayley_table 2 β.primeIndex
def Beta.B (β : Beta) := cayley_table 2 (β.primeIndex + β.d.width)
def Beta.L (β : Beta) := cayley_table (2 + β.d.height) (β.primeIndex)
def Beta.E (β : Beta) := cayley_table (2 + β.d.height) (β.primeIndex + β.d.width)

lemma Beta.primeIndexPos (β : Beta) : 0 < β.primeIndex := primes_inv_pos _ _

lemma Beta.B_def (β : Beta) : β.B = cayley_table 2 (β.primeIndex + β.d.width) := rfl
lemma Beta.E_def (β : Beta) : β.E = cayley_table (2 + β.d.height) (β.primeIndex + β.d.width) := rfl

lemma third_row_lemma {col} (hn : 0 < col) : Nat.Prime (cayley_table 2 col + 3).natAbs :=
by
  unfold cayley_table
  simp [primes_two_eq_three, primes_prime hn]

lemma A_plus_three_is_prime (β : Beta) : Nat.Prime (β.A + 3).natAbs := third_row_lemma β.primeIndexPos
lemma B_plus_three_is_prime (β : Beta) : Nat.Prime (β.B + 3).natAbs := third_row_lemma (β.primeIndexPos.trans_le (Nat.le_add_right _ _))
lemma B_plus_three_minus_E (β : Beta) : Nat.Prime (β.B + 3 - β.E).natAbs :=
by
  rw [Beta.B_def, Beta.E_def]
  unfold cayley_table
  rw [primes_two_eq_three]
  simp
  exact primes_prime (zero_lt_two.trans_le (Nat.le_add_right _ _))

-- ------------------------------------------------------

-- A + E = B + L
lemma able_relationships (β : Beta) : β.A + β.E = β.B + β.L :=
by
  unfold Beta.A Beta.B Beta.L Beta.E cayley_table
  ring
-- ------------------------------------------------------

lemma B_plus_three_minus_prime_equals_E (β : Beta) (_h : Nat.Prime (β.B + 3 - β.E).natAbs) :
  (β.B + 3) - (β.B + 3 - β.E) = β.E :=
by ring

-- -------------------------------------------------------
/-- For a fixed prime P₀ (with 3 < P₀ and P₀ prime), build a Beta from a given Ds by setting P = P₀. -/
noncomputable def beta_fixed (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀) (d : Ds) : Beta :=
{ d          := d,
  P          := P₀,
  three_lt_P := hP₀,
  prime_P    := hp₀ }

/-- beta_fixed is injective since if beta_fixed P₀ hP₀ hp₀ d₁ = beta_fixed P₀ hP₀ hp₀ d₂ then d₁ = d₂. -/
theorem beta_fixed_injective (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀) :
  Function.Injective (beta_fixed P₀ hP₀ hp₀) :=
fun d₁ d₂ h => congr_arg Beta.d h

/-- Define an injection from Ds into the subtype { b : Beta // b.P = P₀ } by mapping d to ⟨beta_fixed P₀ hP₀ hp₀ d, rfl⟩. -/
noncomputable def beta_sub_inj (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀)
  (d : Ds) : { b : Beta // b.P = P₀ } :=
⟨ beta_fixed P₀ hP₀ hp₀ d, rfl ⟩

/-- Prove that beta_sub_inj is injective. -/
theorem beta_sub_inj_injective (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀) :
  Function.Injective (beta_sub_inj P₀ hP₀ hp₀) :=
fun d₁ d₂ h =>
  beta_fixed_injective P₀ hP₀ hp₀ (Subtype.ext_iff.mp h)

/-- An injection from ℕ into Ds is given by mapping n to the Ds instance with y := n + 1, width := n + 1, height := n + 1. -/
noncomputable def ds_inj (n : ℕ) : Ds :=
{ y      := n + 1,
  y_pos  := Nat.succ_pos n,
  width  := n + 1,
  height := n + 1 }

theorem ds_inj_injective : Function.Injective ds_inj :=
fun n m h => Nat.succ.inj (congrArg Ds.y h)

instance : Infinite Ds :=
  Infinite.of_injective ds_inj ds_inj_injective

/-- Since Ds is infinite and beta_sub_inj is injective, the subtype { b : Beta // b.P = P₀ } is infinite. -/
theorem Beta_fixed_infinite (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀) :
  Infinite { b : Beta // b.P = P₀ } :=
Infinite.of_injective (fun d : Ds => ⟨ beta_fixed P₀ hP₀ hp₀ d, rfl ⟩)
  (beta_sub_inj_injective P₀ hP₀ hp₀)
-- ------------------------------------------------------
