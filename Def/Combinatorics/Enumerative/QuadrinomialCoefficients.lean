/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QuadrinomialCoefficients.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators

/-!
# Quadrinomial coefficients

This file formalizes the binomial sum from Remark 3.3 of Zhang,
*Realizability of Some Combinatorial Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex>.
-/


namespace MetaMathlibExt

/-- Zhang's six-parameter binomial sum `V(n, r₁, r₂, s, t, u)`.
The source uses the convention `0 ^ 0 = 1`, which is also Lean's convention
for natural-number powers. -/
def zhangVSum (n r₁ r₂ s t u : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    n.choose k ^ r₁ * n.choose (2 * k) ^ r₂ *
      ((n + k).choose k ^ s * ((2 * k).choose k ^ t * (2 * (n - k)).choose (n - k) ^ u))

/-- The quadrinomial coefficient sequence A005725, expressed as
`∑ k, choose n k * choose n (2 * k)`. -/
def quadrinomialCoeff (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * n.choose (2 * k)

end MetaMathlibExt
