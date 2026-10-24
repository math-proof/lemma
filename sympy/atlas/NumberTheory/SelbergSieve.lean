/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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
