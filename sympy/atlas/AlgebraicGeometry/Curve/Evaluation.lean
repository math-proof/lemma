/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean -/

import sympy.atlas.AlgebraicGeometry.Curve.Divisor
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

/-- Evaluation is the finite product over the support of the divisor. -/
theorem eval_eq_prod (f : C → G) (D : CurveDivisor C) :
    eval f D = D.prod (fun P n ↦ f P ^ n) :=
  rfl

/-- The zero divisor evaluates to one. -/
@[simp]
theorem eval_zero (f : C → G) : eval f (0 : CurveDivisor C) = 1 := by
  simp [eval]

/-- A divisor supported at one point evaluates to the corresponding power. -/
@[simp]
theorem eval_single (f : C → G) (P : C) (n : ℤ) :
    eval f (Finsupp.single P n) = f P ^ n := by
  rw [eval_eq_prod]
  exact Finsupp.prod_single_index (zpow_zero (f P))

/-- Evaluation sends addition of divisors to multiplication. -/
@[simp]
theorem eval_add (f : C → G) (D₁ D₂ : CurveDivisor C) :
    eval f (D₁ + D₂) = eval f D₁ * eval f D₂ := by
  change evalMonoidHom f (Multiplicative.ofAdd D₁ * Multiplicative.ofAdd D₂) =
    evalMonoidHom f (Multiplicative.ofAdd D₁) * evalMonoidHom f (Multiplicative.ofAdd D₂)
  exact map_mul _ _ _

/-- Evaluation sends integer scaling of a divisor to the corresponding power. -/
@[simp]
theorem eval_zsmul (f : C → G) (n : ℤ) (D : CurveDivisor C) :
    eval f (n • D) = eval f D ^ n := by
  change evalMonoidHom f (Multiplicative.ofAdd D ^ n) =
    evalMonoidHom f (Multiplicative.ofAdd D) ^ n
  exact map_zpow _ _ _

end CurveDivisor
