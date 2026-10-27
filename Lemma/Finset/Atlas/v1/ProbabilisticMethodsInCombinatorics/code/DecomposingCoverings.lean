import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.DecomposingCoverings
open Set Metric DecomposingCoverings


namespace DecomposingCoverings

/--
[theorem_6_2_12](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/DecomposingCoverings.lean)
-/
@[path]
lemma theorem_6_2_12
  {center : ι → E3}
  {k : ℕ}
-- given
  (hk : 2 ≤ k)
  (hcov : IsKFoldCovering center k)
  (hindec : ¬ IsDecomposable center) :
-- imply
  ∃ x : E3, (2 : ℝ) ^ ((k : ℝ) / 3) ≤ ↑(mult center x) := by
-- proof
  by_contra h_all_small
  push_neg at h_all_small
  apply hindec
  obtain ⟨A, hA_in, hAc_in⟩ := proper_2coloring_exists ι center k hk hcov h_all_small
  exact ⟨A, fun x => by
    obtain ⟨i, hi_cov, hi_A⟩ := hA_in x
    exact ⟨⟨i, hi_A⟩, by simpa [coveringSet] using hi_cov⟩,
    fun x => by
    obtain ⟨j, hj_cov, hj_notA⟩ := hAc_in x
    exact ⟨⟨j, hj_notA⟩, by simpa [coveringSet] using hj_cov⟩⟩
end



-- created on 2026-10-23
