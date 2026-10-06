import Mathlib
import sympy.Basic

open Polynomial
open scoped Polynomial.Bivariate

/--
[WeierstrassCurve_Affine_evalEval_psi_sq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_evalEval_psi_sq.lean)
-/

private lemma  PortCard.evalEval_ψ_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have hmk : WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n ^ 2) =
      WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
      WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_pow, evalEval_C] at h1
  exact h1

private lemma  PortCard.evalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1
@[main]
private lemma main
  [CommRing R]
  {W : WeierstrassCurve R}
  {x y : R}
  {n : ℤ}
-- given
  (h : W.toAffine.Equation x y) :
-- imply
  (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x :=
-- proof
  PortCard.evalEval_ψ_sq W h n


-- created on 2026-10-05
