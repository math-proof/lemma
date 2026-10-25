/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LensCurvatureRecurrence.lean -/

import Mathlib.Data.Real.Basic


namespace MetaMathlibExt

/-!
# Curvature recurrences for circles in a lens

Source: J. Kocik, *Lens Sequences*, Journal of Integer Sequences 23 (2020),
[`kocik5.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex),
Theorem `thm:abgeo`.
-/

/-- A sequence satisfies the source's second-order nonhomogeneous recurrence for curvatures
of a chain of circles in a symmetric lens. Here `K` is the product of the two lens circles and
`A` is their common curvature. The denominator condition makes explicit the nondegeneracy
used by the source formula. -/
def IsLensCurvatureRecurrence (b : ℕ → ℝ) (K A : ℝ) : Prop :=
  1 + K ≠ 0 ∧ ∀ n,
    b (n + 2) = ((6 - 2 * K) / (1 + K)) * b (n + 1) - b n + (-8 * A) / (1 + K)

end MetaMathlibExt
