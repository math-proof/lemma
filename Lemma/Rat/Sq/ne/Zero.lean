import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


private lemma PortCard.sub_negY_sq_eq_eval_Ψ₂Sq {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  {x y : R} (e : W.toAffine.Equation x y) :
  (y - W.toAffine.negY x y) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Affine.equation_iff] at e
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * e

private lemma PortCard.two_smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
  2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 := by
  have key : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ y = W.toAffine.negY x y := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    simp
  rw [key, ← PortCard.sub_negY_sq_eq_eval_Ψ₂Sq W h.left, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

private lemma PortCard.Ψ₂Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F)
  [W.IsElliptic] : W.Ψ₂Sq ≠ 0 := by
  intro h0
  rw [WeierstrassCurve.Ψ₂Sq_eq, Cubic.toPoly_eq_zero_iff] at h0
  have h4 : (4 : F) = 0 := congrArg Cubic.a h0
  have hb₂ : W.b₂ = 0 := congrArg Cubic.b h0
  have hb₆ : W.b₆ = 0 := congrArg Cubic.d h0
  have h2 : (2 : F) = 0 := by
    have h22 : (2 : F) * 2 = 0 := by linear_combination h4
    obtain h | h := mul_eq_zero.mp h22 <;> exact h
  have hΔ : W.Δ = 0 := by
    rw [show W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
      from rfl]
    linear_combination (-W.b₂ * W.b₈ + 9 * W.b₄ * W.b₆) * hb₂ + (-27 * W.b₆) * hb₆ +
      (-4 * W.b₄ ^ 3) * h2
  refine W.isUnit_Δ.ne_zero hΔ
/--
[WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic.lean)
-/
@[path]
private lemma main
  [Field F]
  {W : WeierstrassCurve F} [W.IsElliptic] :
-- imply
  W.Ψ₂Sq ≠ 0 :=
-- proof
  PortCard.Ψ₂Sq_ne_zero_of_isElliptic W


-- created on 2026-10-23
