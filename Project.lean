import Mathlib

set_option linter.unusedTactic false 
set_option linter.unusedVariables false 

-- ------------------------------------------------------
-- define the cayley table - infinitely defined
-- ------------------------------------------------------

def primes_set := { n | Nat.Prime n }

instance : Infinite primes_set := Nat.infinite_setOf_prime.to_subtype
instance : DecidablePred (fun n => n ∈ primes_set) := 
fun n => Nat.decidablePrime n

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

-- ------------------------------------------------------
-- define the cayley table data structure - sub arrays
-- ------------------------------------------------------
/-- Structure Ds holds the variable data. -/
structure Ds where
  y            : ℕ
  y_pos        : y > 0
  x            : ℤ
  width        : ℕ
  height       : ℕ
  B            : ℤ 
  L            : ℤ 

/-- Structure Beta holds the variable & static data. -/
structure Beta where
  d            : Ds 
  P            : ℕ
  three_lt_P   : 3 < P := by decide
  prime_P      : Nat.Prime P := by decide
  primeIndex   : ℕ := primes_inv P prime_P
  k            : ℕ
  k_pos        : k > 0
  k_x_y        : k = d.x + ↑d.y
  A            : ℤ := cayley_table 2 primeIndex
  h1_A         : A = (P : ℤ) - 3
  h2_A         : A = 6 * d.x + 6 * (↑d.y) - 
                     (if P = 6 * (d.x + ↑d.y) - 1 then 4 else if P = 6 * (d.x + ↑d.y) + 1 then 2 else 0)
  h1_B         : d.B = cayley_table 2 (primeIndex + 
                                       d.width)
  h2_B         : d.B = 6 * d.x + 12 * (↑d.y) - 
                       (if P = 6 * (d.x + ↑d.y) - 1 then 8 else if P = 6 * (d.x + ↑d.y) + 1 then 4 else 0)
  h1_L         : d.L = cayley_table (2 + d.height) 
                                    (primeIndex)
  h2_L         : d.L = 6 * d.x
  E            : ℤ := cayley_table (2 + d.height) 
                                   (primeIndex + d.width)
  h1_E         : E = A
  h2_E         : E = 6 * d.x + 6 * (↑d.y) - 
                     (if P = 6 * (d.x + ↑d.y) - 1 then 4 else if P = 6 * (d.x + ↑d.y) + 1 then 2 else 0)

-- ------------------------------------------------------
-- prove that Beta is infinite.
-- ------------------------------------------------------

/-- We now define a function beta_fixed that builds a Beta from a Ds instance by fixing P,
    k, and the corresponding proofs. -/
noncomputable def beta_fixed 
  (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀)
  (d : Ds ) (hk₀ : ℕ) (hkpos₀ : hk₀ > 0) (hkxy₀ : hk₀ = d.x + ↑d.y) (primeIndex₀ : ℕ)
  (A_val : ℤ) (h1A : A_val = (P₀ : ℤ) - 3) 
  (h2A : A_val = 6 * d.x + 6 * (↑d.y) - 
                     (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
  (h1B : d.B = cayley_table 2 (primeIndex₀ + d.width))
  (h2B : d.B = 6 * d.x + 12 * (↑d.y) - 
                       (if P₀ = 6 * (d.x + ↑d.y) - 1 then 8 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 4 else 0))
  (h1L : d.L = cayley_table (2 + d.height) (primeIndex₀))
  (h2L : d.L = 6 * d.x)
  (E_val : ℤ) (h1E : E_val = A_val)
  (h2E : E_val = 6 * d.x + 6 * (↑d.y) - 
                     (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))                   
  : Beta :=
{ d          := d,
  P          := P₀,
  three_lt_P := hP₀,
  prime_P    := hp₀,
  primeIndex := primeIndex₀,
  k          := hk₀,
  k_pos      := hkpos₀,
  k_x_y      := hkxy₀, 
  A          := A_val,
  h1_A       := h1A,
  h2_A       := h2A,
  h1_B       := h1B,
  h2_B       := h2B,
  h1_L       := h1L,
  h2_L       := h2L,
  E          := E_val,
  h1_E       := h1E,  
  h2_E       := h2E
  }
-- ------------------------------------------------------
/-- Define a wrapper beta_fixed' that fixes all parameters except the variable data d. -/

noncomputable def beta_fixed' 
  (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀)
  (hk₀ : ℕ) (hkpos₀ : hk₀ > 0) (hkxy₀ : ∀ d : Ds, hk₀ = d.x + ↑d.y) (primeIndex₀ : ℕ)
  (A_val : ℤ) (h1A : A_val = (P₀ : ℤ) - 3) 
  (h2A : ∀ d : Ds, A_val = 6 * d.x + 6 * (↑d.y) - (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
  (h1B : ∀ d : Ds, d.B = cayley_table 2 (primeIndex₀ + d.width))
  (h2B : ∀ d : Ds, d.B = 6 * d.x + 12 * (↑d.y) - 
                       (if P₀ = 6 * (d.x + ↑d.y) - 1 then 8 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 4 else 0))
  (h1L : ∀ d : Ds, d.L = cayley_table (2 + d.height) (primeIndex₀))
  (h2L : ∀ d : Ds, d.L = 6 * d.x)

  (E_val : ℤ) (h1E : E_val = A_val)
  (h2E :  ∀ d : Ds, E_val = 6 * d.x + 6 * (↑d.y) - 
  (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else 
   if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))

 : Ds → Beta :=
  fun d => beta_fixed P₀ hP₀ hp₀ d hk₀ hkpos₀ (hkxy₀ d) primeIndex₀ A_val h1A (h2A d) (h1B d) (h2B d) (h1L d) (h2L d) E_val h1E (h2E d)

-- ------------------------------------------------------
/-- Prove that beta_fixed' is injective; that is, if two Beta values built by beta_fixed' are equal,
    then the underlying Ds instances are equal. -/
theorem beta_fixed'_injective 
  (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀)
  (hk₀ : ℕ) (hkpos₀ : hk₀ > 0) (hkxy₀ : ∀ d : Ds, hk₀ = d.x + ↑d.y)
 (primeIndex₀ : ℕ)
  (A_val : ℤ) (h1A : A_val = (P₀ : ℤ) - 3) 
  (h2A : ∀ d : Ds, A_val = 6 * d.x + 6 * (↑d.y) - (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
  (h1B : ∀ d : Ds, d.B = cayley_table 2 (primeIndex₀ + d.width))
  (h2B : ∀ d : Ds, d.B = 6 * d.x + 12 * (↑d.y) - 
                       (if P₀ = 6 * (d.x + ↑d.y) - 1 then 8 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 4 else 0))
  (h1L : ∀ d : Ds, d.L = cayley_table (2 + d.height) (primeIndex₀))
  (h2L : ∀ d : Ds, d.L = 6 * d.x)

  (E_val : ℤ) (h1E : E_val = A_val)
  (h2E :  ∀ d : Ds, E_val = 6 * d.x + 6 * (↑d.y) - 
  (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else 
   if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0)) :
  Function.Injective (beta_fixed' P₀ hP₀ hp₀ hk₀ hkpos₀ 
  (hkxy₀) primeIndex₀ A_val h1A (h2A) (h1B) (h2B) (h1L) (h2L) E_val h1E (h2E)) :=
fun d₁ d₂ h => congr_arg Beta.d h

-- ------------------------------------------------------
/-- Define an injection from Ds into the subtype { b : Beta // b.P = P₀ } by mapping d to
    ⟨beta_fixed' P₀ ... d, rfl⟩. -/
noncomputable def beta_sub_inj 
  (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀)
  (hk₀ : ℕ) (hkpos₀ : hk₀ > 0) (hkxy₀ : ∀ d : Ds, hk₀ = d.x + ↑d.y)

 (primeIndex₀ : ℕ)
  (A_val : ℤ) (h1A : A_val = (P₀ : ℤ) - 3) 
  (h2A : ∀ d : Ds, A_val = 6 * d.x + 6 * (↑d.y) - (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
  (h1B : ∀ d : Ds, d.B = cayley_table 2 (primeIndex₀ + d.width))
  (h2B : ∀ d : Ds, d.B = 6 * d.x + 12 * (↑d.y) - 
                       (if P₀ = 6 * (d.x + ↑d.y) - 1 then 8 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 4 else 0))
  (h1L : ∀ d : Ds, d.L = cayley_table (2 + d.height) (primeIndex₀))
  (h2L : ∀ d : Ds, d.L = 6 * d.x)

  (E_val : ℤ) (h1E : E_val = A_val)
  (h2E :  ∀ d : Ds, E_val = 6 * d.x + 6 * (↑d.y) - 
  (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else 
   if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
  (d : Ds) : { b : Beta // b.P = P₀ } :=
⟨ beta_fixed' P₀ hP₀ hp₀ hk₀ hkpos₀ 
  (hkxy₀) primeIndex₀ A_val h1A (h2A) (h1B) (h2B) (h1L) (h2L) E_val h1E (h2E) d, rfl⟩

-- ------------------------------------------------------
/-- Prove that beta_sub_inj is injective. -/
theorem beta_sub_inj_injective 
  (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀)
  (hk₀ : ℕ) (hkpos₀ : hk₀ > 0) (hkxy₀ : ∀ d : Ds, hk₀ = d.x + ↑d.y)

 (primeIndex₀ : ℕ)
  (A_val : ℤ) (h1A : A_val = (P₀ : ℤ) - 3) 
  (h2A : ∀ d : Ds, A_val = 6 * d.x + 6 * (↑d.y) - (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
  (h1B : ∀ d : Ds, d.B = cayley_table 2 (primeIndex₀ + d.width))
  (h2B : ∀ d : Ds, d.B = 6 * d.x + 12 * (↑d.y) - 
                       (if P₀ = 6 * (d.x + ↑d.y) - 1 then 8 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 4 else 0))
  (h1L : ∀ d : Ds, d.L = cayley_table (2 + d.height) (primeIndex₀))
  (h2L : ∀ d : Ds, d.L = 6 * d.x)

  (E_val : ℤ) (h1E : E_val = A_val)
  (h2E :  ∀ d : Ds, E_val = 6 * d.x + 6 * (↑d.y) - 
  (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else 
   if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
  
  :
  Function.Injective (beta_sub_inj P₀ hP₀ hp₀ hk₀ hkpos₀ hkxy₀ primeIndex₀ A_val h1A (h2A) (h1B) (h2B) (h1L) (h2L) E_val h1E (h2E)) :=

fun d₁ d₂ h =>
  beta_fixed'_injective P₀ hP₀ hp₀ hk₀ hkpos₀ hkxy₀ primeIndex₀ A_val h1A (h2A) (h1B) (h2B) (h1L) (h2L) E_val h1E (h2E) (Subtype.ext_iff.mp h)

-- ------------------------------------------------------
/-- An injection from ℕ into Ds is given by mapping n to the Ds instance with all fields set to n+1 (or n+1 for x, width, height). -/
noncomputable def ds_inj (n : ℕ) : Ds :=
{ y      := n + 1,
  y_pos  := Nat.succ_pos n,
  x      := n + 1,
  width  := n + 1,
  height := n + 1,
  B      := n + 1,
  L      := n + 1 }

-- ------------------------------------------------------
theorem ds_inj_injective : Function.Injective ds_inj :=
fun n m h => Nat.succ.inj (congrArg Ds.y h)

-- ------------------------------------------------------
instance : Infinite Ds :=
  Infinite.of_injective ds_inj ds_inj_injective

-- ------------------------------------------------------
/-- Since Ds is infinite and beta_sub_inj is injective, the subtype { b : Beta // b.P = P₀ } is infinite. -/
theorem Beta_fixed_infinite (P₀ : ℕ) (hP₀ : 3 < P₀) (hp₀ : Nat.Prime P₀)
  (hk₀ : ℕ) (hkpos₀ : hk₀ > 0) (hkxy₀ : ∀ d : Ds, hk₀ = d.x + ↑d.y)

 (primeIndex₀ : ℕ)
  (A_val : ℤ) (h1A : A_val = (P₀ : ℤ) - 3) 
  (h2A : ∀ d : Ds, A_val = 6 * d.x + 6 * (↑d.y) - (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
  (h1B : ∀ d : Ds, d.B = cayley_table 2 (primeIndex₀ + d.width))
  (h2B : ∀ d : Ds, d.B = 6 * d.x + 12 * (↑d.y) - 
                       (if P₀ = 6 * (d.x + ↑d.y) - 1 then 8 else if P₀ = 6 * (d.x + ↑d.y) + 1 then 4 else 0))
  (h1L : ∀ d : Ds, d.L = cayley_table (2 + d.height) (primeIndex₀))
  (h2L : ∀ d : Ds, d.L = 6 * d.x)

  (E_val : ℤ) (h1E : E_val = A_val)
  (h2E :  ∀ d : Ds, E_val = 6 * d.x + 6 * (↑d.y) - 
  (if P₀ = 6 * (d.x + ↑d.y) - 1 then 4 else 
   if P₀ = 6 * (d.x + ↑d.y) + 1 then 2 else 0))
 
  :
  Infinite { b : Beta // b.P = P₀ } :=
Infinite.of_injective (fun d : Ds => ⟨ beta_fixed' P₀ hP₀ hp₀ hk₀ hkpos₀ (hkxy₀) primeIndex₀ A_val h1A (h2A) (h1B) (h2B) (h1L) (h2L) E_val h1E (h2E) d, rfl⟩)
  (beta_sub_inj_injective P₀ hP₀ hp₀ hk₀ hkpos₀ hkxy₀ 
  primeIndex₀ A_val h1A (h2A) (h1B) (h2B) (h1L) (h2L) E_val h1E (h2E))

-- ------------------------------------------------------