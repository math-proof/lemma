/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean -/

import Def.AlgebraicGeometry.Curve.Divisor
import Lemma.Finsupp.EqCoeff_Single
import Mathlib.Algebra.BigOperators.Finsupp.Basic
/-!
# Evaluation of curve divisors

This file defines the generic algebraic evaluation of a divisor against a function into a
commutative group. It does not impose rational-function or disjoint-support hypotheses.
-/


namespace CurveDivisor

variable {C G : Type*} [CommGroup G]

/-- The multiplicative homomorphism underlying evaluation of divisors against `f`. -/
noncomputable def evalMonoidHom (f : C → G) : Multiplicative (CurveDivisor C) →* G where
  toFun D := D.toAdd.prod fun P n ↦ f P ^ n
  map_one' := by simp
  map_mul' D₁ D₂ :=
    Finsupp.prod_add_index' (fun P ↦ zpow_zero (f P))
      (fun P n₁ n₂ ↦ zpow_add (f P) n₁ n₂)

/-- Evaluate a divisor by multiplying the corresponding integer powers of `f`. -/
noncomputable def eval (f : C → G) (D : CurveDivisor C) : G :=
  evalMonoidHom f (Multiplicative.ofAdd D)

end CurveDivisor
