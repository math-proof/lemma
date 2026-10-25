import Mathlib
import sympy.Basic
import Theorem.Analysis.NormedSpace.BrowderKirk.Part2

open FunctionalAnalysis.BrowderKirkWanted Set

/--
[browderGoehdeKirk_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/BrowderKirk.lean)
-/
@[path]
private lemma browder_goehde_kirk_fixed_point_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E] [CompleteSpace E]
  {K : Set E} {f : E → E}
  (hK_nonempty : K.Nonempty)
  (hK_closed : IsClosed K)
  (hK_bounded : Bornology.IsBounded K)
  (hK_convex : Convex ℝ K)
  (hf_maps : MapsTo f K K)
  (hf_lip : LipschitzOnWith 1 f K) :
-- imply
  ∃ y ∈ K, f y = y := by
-- proof
  apply browderGoehdeKirk_fixedPoint hK_nonempty hK_closed hK_bounded hK_convex hf_maps hf_lip

-- created on 2026-10-10
