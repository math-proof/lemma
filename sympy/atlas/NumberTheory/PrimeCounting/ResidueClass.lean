/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClass.lean -/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.ModEq

/-!
# Prime counting in a residue class

This file defines the inclusive finite count of primes in one residue class.
-/

namespace Nat

/-- The number of primes `p ≤ X` with `p ≡ a [MOD q]`.

Uses `Nat.primesLE` so the inclusive endpoint and primality
filter are not rebuilt. `q = 1` is admitted. -/
def primeCountingMod (X q a : ℕ) : ℕ :=
  ((X.primesLE.filter fun p => p ≡ a [MOD q]).card)

/-- Modulus one imposes no residue condition, so the count
reduces to the ordinary prime-counting function. -/
theorem primeCountingMod_one (X a : ℕ) :
    primeCountingMod X 1 a = Nat.primeCounting X := by
  unfold primeCountingMod
  have hfilter : (X.primesLE.filter fun p => p ≡ a [MOD 1]) = X.primesLE := by
    apply Finset.filter_true_of_mem
    intro p _
    simp [Nat.ModEq, Nat.mod_one]
  rw [hfilter, Nat.primesLE_card_eq_primeCounting]

/-- The residue-class prime count as a range filtered by primality and congruence. -/
theorem primeCountingMod_eq_card_filter_range (n q a : ℕ) :
    Nat.primeCountingMod n q a
      = ((Finset.range (n + 1)).filter
        fun p => Nat.Prime p ∧ Nat.ModEq q p a).card := by
  unfold Nat.primeCountingMod
  rw [Nat.primesLE_eq_filter_range, Finset.filter_filter]

end Nat
