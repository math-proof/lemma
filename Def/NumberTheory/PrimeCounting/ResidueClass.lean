/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClass.lean -/

module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.ModEq

@[expose] public section

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

end Nat
