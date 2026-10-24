import Mathlib
import sympy.Basic
open Polynomial


/--
[WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff.lean)
-/
@[path]
private lemma main
  [Field F] [DecidableEq F]
  {W : WeierstrassCurve F}
  {x y : F}
-- given
  (h : W.toAffine.Nonsingular x y) :
-- imply
  2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 := by
-- proof
  have sub_negY : (y - W.toAffine.negY x y) ^ 2 = W.Ψ₂Sq.eval x := by
    have e := h.left
    rw [WeierstrassCurve.Affine.equation_iff] at e
    simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination 4 * e
  have key : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ y = W.toAffine.negY x y := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    simp
  rw [key, ← sub_negY, pow_eq_zero_iff two_ne_zero, sub_eq_zero]


-- created on 2026-10-24
