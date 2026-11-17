/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Selberg sieve level weights

This module defines the optimal level-`R` Selberg weights for an arbitrary
`BoundingSieve` and proves their diagonalization, support, and error bounds.
-/


namespace MathlibExt.SelbergSieve

/-- The Selberg level set consists of the divisors of `s.prodPrimes` at most `R`. -/
def levelSet (s : BoundingSieve) (R : ℕ) : Finset ℕ :=
  s.prodPrimes.divisors.filter fun l ↦ l ≤ R

/-- The Selberg level sum is the sum of `s.selbergTerms` over the level set. -/
noncomputable def levelSum (s : BoundingSieve) (R : ℕ) : ℝ :=
  ∑ l ∈ levelSet s R, s.selbergTerms l

/-- The normalized Selberg `y`-coefficient at `l`, extended by zero off the level set. -/
noncomputable def levelY
    (s : BoundingSieve) (R l : ℕ) : ℝ :=
  if l ∈ levelSet s R then
    ((ArithmeticFunction.moebius l : ℤ) : ℝ) * s.selbergTerms l /
      levelSum s R
  else 0

/-- The level-`R` Selberg weights obtained from the normalized `y`-coefficients by
Moebius inversion. -/
noncomputable def levelWeights
    (s : BoundingSieve) (R d : ℕ) : ℝ :=
  (s.nu d)⁻¹ * ∑ m ∈ s.prodPrimes.divisors,
    if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
      levelY s R m else 0

end MathlibExt.SelbergSieve
