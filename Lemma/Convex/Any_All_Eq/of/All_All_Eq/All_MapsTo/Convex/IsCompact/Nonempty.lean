import Mathlib
import sympy.Basic
import Theorem.Analysis.NormedSpace.MarkovKakutani

open Set

/--
[MarkovKakutani](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/MarkovKakutani.lean)
-/
@[path]
private lemma markov_kakutani_common_fixed_point_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E}
  {ι : Type*}
  (F : ι → ContinuousAffineMap ℝ E E)
  (hK_nonempty : K.Nonempty)
  (hK_compact : IsCompact K)
  (hK_convex : Convex ℝ K)
  (hF_maps : ∀ i, MapsTo (F i) K K)
  (hF_comm : ∀ i j : ι, ∀ x : E, F i (F j x) = F j (F i x)) :
-- imply
  ∃ x ∈ K, ∀ i, F i x = x := by
-- proof
  apply FunctionalAnalysis.MarkovKakutani.markovKakutani_commonFixedPoint hK_nonempty hK_compact hK_convex F hF_maps hF_comm

-- created on 2026-10-10
