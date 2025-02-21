import Mathlib

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
-- --------------------------------------------------------------------------------------------------------------------------
lemma primes_two_eq_three : primes 2 = 3 := by native_decide

structure Beta where
P          : ℕ
width      : ℕ
height     : ℕ
three_lt_P : 3 < P := by decide
prime_P    : Nat.Prime P := by decide

def Beta.primeIndex (β : Beta) := primes_inv β.P β.prime_P

def Beta.A (β : Beta) := cayley_table 2 β.primeIndex
def Beta.B (β : Beta) := cayley_table 2 (β.primeIndex + β.width)
def Beta.L (β : Beta) := cayley_table (2 + β.height) (β.primeIndex)
def Beta.E (β : Beta) := cayley_table (2 + β.height) (β.primeIndex + β.width)

lemma Beta.primeIndexPos (β : Beta) : 0 < β.primeIndex := primes_inv_pos _ _

lemma Beta.B_def (β : Beta) : β.B = cayley_table 2 (β.primeIndex + β.width) := rfl
lemma Beta.E_def (β : Beta) : β.E = cayley_table (2 + β.height) (β.primeIndex + β.width) := rfl

lemma third_row_lemma {col} (hn : 0 < col) : Nat.Prime (cayley_table 2 col + 3).natAbs :=
by
  unfold cayley_table
  simp [primes_two_eq_three, primes_prime hn]
-- --------------------------------------------------------------------------------------------------------------------------
example (β : Beta) : Nat.Prime (β.A + 3).natAbs := third_row_lemma β.primeIndexPos
example (β : Beta) : Nat.Prime (β.B + 3).natAbs := third_row_lemma (β.primeIndexPos.trans_le (Nat.le_add_right _ _))
example (β : Beta) : Nat.Prime (β.B + 3 - β.E).natAbs :=
by
  rw [Beta.B_def, Beta.E_def]
  unfold cayley_table
  rw [primes_two_eq_three]
  simp
  exact primes_prime (zero_lt_two.trans_le (Nat.le_add_right _ _))
-- --------------------------------------------------------------------------------------------------------------------------
-- A + E = B + L
example (β : Beta) : β.A + β.E = β.B + β.L :=
by
  unfold Beta.A Beta.B Beta.L Beta.E cayley_table
  ring
-- --------------------------------------------------------------------------------------------------------------------------

def Beta.isPrimeArrayWith (β : Beta) (X Y : ℕ) : Prop :=
β.A = 6 * X + 6 * Y - (
  if β.P = 6 * (X + Y) - 1 then 4
  else if β.P = 6 * (X + Y) + 1 then 2
  else 0
) ∧
β.B = 6 * X + 12 * Y - (
  if β.P = 6 * (X + Y) - 1 then 8
  else if β.P = 6 * (X + Y) + 1 then 4
  else 0
) ∧
β.L = 6 * X ∧
β.E = β.A

-- --------------------------------------------------------------------------------------------------------------------------
instance (β : Beta) (X Y : ℕ) : Decidable (β.isPrimeArrayWith X Y) := instDecidableAnd

def Beta.isPrimeArray (β : Beta) : Prop :=
∃ X Y, β.isPrimeArrayWith X Y

def PrimeArray : Type := { β : Beta // β.isPrimeArray }

-- --------------------------------------------------------------------------------------------------------------------------

def x : Beta := {
  P          := 23
  width      := 2
  height     := 3
}
#eval (x.A, x.B, x.L, x.E)
#eval x.isPrimeArrayWith 2 2
#eval (x.B + 3)
-- -- --
lemma x_is_prime_array : x.isPrimeArray :=
⟨2, 2, by native_decide⟩ -- Demonstrating that x satisfies the condition.
-- --------------------------------------------------------------------------------------------------------------------------

lemma PrimeArray_exists : ∃ β : Beta, β.isPrimeArray :=
by
  let x : Beta := {
    P          := 23,
    width      := 2,
    height     := 3
  }
  use x
  use 2
  use 2
  native_decide
-- --------------------------------------------------------------------------------------------------------------------------

lemma PrimeArray_exists_iff_Beta_exists :
  (∃ _ : PrimeArray, True) ↔ (∃ β : Beta, β.isPrimeArray) :=
  {
    mp := fun ⟨pa, _⟩ =>
      Exists.intro pa.val pa.property,
    mpr := fun ⟨β, h⟩ =>
      Exists.intro ⟨β, h⟩ trivial
  }
-- --------------------------------------------------------------------------------------------------------------------------

class IsPrimeArray (b : Beta) where
(X Y : ℕ)
(hb : b.isPrimeArrayWith X Y)
-- --------------------------------------------------------------------------------------------------------------------------

def Beta.X (b : Beta) [IsPrimeArray b] : ℕ := IsPrimeArray.X b
def Beta.Y (b : Beta) [IsPrimeArray b] : ℕ := IsPrimeArray.Y b
def Beta.Prime (b : Beta) [IsPrimeArray b] : b.isPrimeArrayWith b.X b.Y := IsPrimeArray.hb

-- --------------------------------------------------------------------------------------------------------------------------

#eval (x.A, x.B, x.L, x.E)
#eval x.isPrimeArrayWith 2 2

-- --------------------------------------------------------------------------------------------------------------------------

lemma one (b : Beta) [IsPrimeArray b] (h : b.P = 6 * (b.X + b.Y) - 1)
  : b.B + 3 = (6 * b.X + 6 * b.Y - 1) + (6 * b.Y - 1) - 3 :=
by
  obtain ⟨h1, h2, h3, h4⟩ := b.Prime
  simp_all
  ring

-- --------------------------------------------------------------------------------------------------------------------------

theorem Infinite_Primearray : Set.Infinite Beta.isPrimeArray := sorry
-- --------------------------------------------------------------------------------------------------------------------------
