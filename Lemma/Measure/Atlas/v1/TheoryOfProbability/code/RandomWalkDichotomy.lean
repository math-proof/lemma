import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.RandomWalkDichotomy
open MeasureTheory ProbabilityTheory Filter Finset Topology


/--
[exists_prob_one_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/RandomWalkDichotomy.lean)
-/
@[path]
lemma exists_prob_one_of_cover
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {E₁ E₂ E₃ E₄ : Set Ω}
-- given
  (h_cover : μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄)ᶜ = 0)
  (h0 : μ E₁ = 0 ∨ μ E₁ = 1)
  (h1 : μ E₂ = 0 ∨ μ E₂ = 1)
  (h2 : μ E₃ = 0 ∨ μ E₃ = 1)
  (h3 : μ E₄ = 0 ∨ μ E₄ = 1) :
-- imply
  μ E₁ = 1 ∨ μ E₂ = 1 ∨ μ E₃ = 1 ∨ μ E₄ = 1 := by
-- proof
  by_contra h_none
  simp only [not_or] at h_none
  obtain ⟨hne1, hne2, hne3, hne4⟩ := h_none
  have he1 : μ E₁ = 0 := h1.resolve_right hne1
  have he2 : μ E₂ = 0 := h2.resolve_right hne2
  have he3 : μ E₃ = 0 := h3.resolve_right hne3
  have he4 : μ E₄ = 0 := h4.resolve_right hne4
  have h_union : μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄) = 0 := by
    have h12 : μ (E₁ ∪ E₂) = 0 :=
      nonpos_iff_eq_zero.mp (le_trans (measure_union_le E₁ E₂) (by simp [he1, he2]))
    have h123 : μ (E₁ ∪ E₂ ∪ E₃) = 0 :=
      nonpos_iff_eq_zero.mp (le_trans (measure_union_le _ E₃) (by simp [h12, he3]))
    exact nonpos_iff_eq_zero.mp (le_trans (measure_union_le _ E₄) (by simp [h123, he4]))
  have h_le := measure_univ_le_add_compl (μ := μ) (E₁ ∪ E₂ ∪ E₃ ∪ E₄)
  rw [h_union, h_cover, add_zero, measure_univ] at h_le
  exact absurd h_le (by norm_num)


-- created on 2026-10-23
