import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.PowerGrowthBadSet

open Real.Calculus.PowerGrowthBadSet
open Set MeasureTheory
open scoped ENNReal

/--
[volume_powerGrowthBadSet_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/PowerGrowthBadSet.lean)
-/
@[path]
private lemma volume_powerGrowthBadSet_lt_top_eq
-- given
  (h : ℝ → ℝ) {p x0 : ℝ} (hp : 1 < p)
  (hpos : ∀ x, x0 ≤ x → 0 < h x)
  (hmono : MonotoneOn h (Ici x0))
  (hsmooth : ContDiff ℝ 1 h) :
-- imply
  volume (powerGrowthBadSet h p x0) < ∞ := by
-- proof
  apply volume_powerGrowthBadSet_lt_top h hp hpos hmono hsmooth


-- created on 2026-10-09
