import Mathlib
import sympy.Basic

open WeierstrassCurve.Affine.Point

/--
[WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY.lean)
-/
@[main]
private lemma main
  [Field F] [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {x y : F}
-- given
  (h : W.Nonsingular x y) :
-- imply
  2 • (some _ _ h : W.Point) = 0 ↔ y = W.negY x y := by
-- proof
  rw [two_nsmul, add_eq_zero_iff_eq_neg, neg_some]
  exact ⟨fun hP => (some.inj hP).right, fun hy => by simp only [some.injEq]; exact ⟨trivial, hy⟩⟩


-- created on 2026-10-03
