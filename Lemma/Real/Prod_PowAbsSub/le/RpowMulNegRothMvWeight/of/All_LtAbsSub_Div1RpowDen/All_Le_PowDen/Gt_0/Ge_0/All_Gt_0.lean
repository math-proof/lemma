import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Real.Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LeAbsSub_RpowDivNeg.Gt_0
import Lemma.Real.AbsSub.le.RpowDivNeg.of.LtAbsSub_Div1RpowDen.Le_PowDen.Gt_0.Ge_0.Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Real


/--
[roth_product_approximation_bound_of_den_power](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (x : Fin m → ℝ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (a Q : ℝ)
-- given
  (hr : ∀ h, 0 < r h)
  (ha : 0 ≤ a)
  (hQ : 0 < Q)
  (hpower : ∀ h, Q ≤ ((q h).den : ℝ) ^ r h)
  (happrox : ∀ h,
    |x h - (q h : ℝ)| < 1 / Real.rpow ((q h).den : ℝ) a) :
-- imply
  ∀ l : RothMvIndex m,
    ∏ h, |(q h : ℝ) - x h| ^ l h ≤
      Real.rpow Q (-a * rothMvWeight r l) := by
-- proof
  apply Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LeAbsSub_RpowDivNeg.Gt_0 x q r Q a hQ
  intro h
  exact AbsSub.le.RpowDivNeg.of.LtAbsSub_Div1RpowDen.Le_PowDen.Gt_0.Ge_0.Gt_0
    (q h) (r h) a Q (hr h) ha hQ (hpower h) (happrox h)


-- created on 2026-10-21
