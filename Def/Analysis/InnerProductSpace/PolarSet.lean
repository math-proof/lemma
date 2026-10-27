import Mathlib.Analysis.InnerProductSpace.Basic
/-!
# Polar of a set in a real inner-product space

This module defines the convex-geometry **polar** of a set `A` in a real
inner-product space `E`:
`A° = {y : E | ∀ x ∈ A, ⟪x, y⟫_ℝ ≤ 1}`.

The convention is the one-sided real inner-product bound `⟪x, y⟫_ℝ ≤ 1`, as used
in convex geometry and polar duality (the bipolar theorem for convex bodies).

This is deliberately distinct from the API already in Mathlib:

* `LinearMap.polar B A = {y | ∀ x ∈ A, ‖B x y‖ ≤ 1}` takes the **absolute
  value / norm** `‖·‖ ≤ 1` (the balanced/symmetric polar). Specialized to an
  inner-product pairing it can be compared with `polarSet` in the same space,
  and the two agree when `A` is closed under negation (in particular, when `A`
  is balanced). `NormedSpace.polar A` instead lives in the continuous dual
  space; its preimage under the inner-product embedding `E → (E →L[ℝ] ℝ)` is
  `{y | ∀ x ∈ A, |⟪x, y⟫_ℝ| ≤ 1}` (a norm-based, hence balanced, variant),
  which agrees with the one-sided `polarSet A` only when `A` is closed under
  negation. Without that hypothesis the two are distinct comparable
  constructions, and identifying the dual with `E` itself would additionally
  need completeness/Riesz hypotheses not assumed here.
* `Set.innerDualCone` / `PointedCone.dual` use the sign condition `0 ≤ ⟪x, y⟫`
  (the inner dual cone), not `≤ 1`.
* `Submodule.dualAnnihilator` uses the linear condition `= 0`.

The inner product is written `inner ℝ x y`, i.e. `𝕜 = ℝ` made explicit.
-/


namespace InnerProductSpace.PolarSet.MetaMathlibExt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The polar of a set `A` in a real inner-product space:
`polarSet A = {y | ∀ x ∈ A, ⟪x, y⟫_ℝ ≤ 1}`, using the one-sided real
inner-product convention `⟪x, y⟫_ℝ ≤ 1`. -/
def polarSet (A : Set E) : Set E := {y | ∀ x ∈ A, inner ℝ x y ≤ 1}

end InnerProductSpace.PolarSet.MetaMathlibExt
