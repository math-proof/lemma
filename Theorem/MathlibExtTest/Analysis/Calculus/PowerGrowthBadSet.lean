/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/PowerGrowthBadSet.lean -/


import Def.Analysis.Calculus.PowerGrowthBadSet
import Lemma.Real.Calculus.PowerGrowthBadSet
open MeasureTheory Set
open scoped ENNReal


example (h : ℝ → ℝ) {p x₀ : ℝ} (hp : 1 < p)
    (hpos : ∀ x, x₀ ≤ x → 0 < h x)
    (hmono : MonotoneOn h (Ici x₀))
    (hsmooth : ContDiff ℝ 1 h) :
    volume (Real.powerGrowthBadSet h p x₀) < ∞ :=
  Real.volume_powerGrowthBadSet_lt_top h hp hpos hmono hsmooth

