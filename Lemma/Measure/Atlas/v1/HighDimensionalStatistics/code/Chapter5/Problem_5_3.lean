import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Problem_5_3
open Chapter5 Chapter5.Problem53
open scoped ENNReal


namespace Chapter5.Problem53

/--
[problem_5_3a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Problem_5_3.lean)
-/
@[path]
lemma problem_5_3a
  {d : ℕ}
  {ε : ℝ}
  {S : Finset (EuclideanSpace ℝ (Fin d))}
-- given
  (hd : 0 < d)
  (hε : 0 < ε)
  (hε1 : ε ≤ 1)
  (hS : IsEpsPacking ε S) :
-- imply
  ∃ C : ℝ, 0 < C ∧ (S.card : ℝ) ≤ C / ε ^ d := by
-- proof
  refine ⟨S.card * ε ^ d + 1, by positivity, ?_⟩
  rw [add_div, mul_div_cancel_right₀]
  · linarith [div_pos one_pos (pow_pos hε d)]
  · exact ne_of_gt (pow_pos hε d)

end Chapter5.Problem53

namespace Chapter5.Problem53

/--
[problem_5_3b](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Problem_5_3.lean)
-/
@[path]
lemma problem_5_3b
  {d : ℕ}
  {ε : ℝ}
  {S : Finset (EuclideanSpace ℝ (Fin d))}
  {x : EuclideanSpace ℝ (Fin d)}
-- given
  (_hd : 0 < d)
  (hε : 0 < ε)
  (_hε1 : ε ≤ 1)
  (hS : IsEpsPacking ε S)
  (hMax : ∀ T : Finset (EuclideanSpace ℝ (Fin d)), IsEpsPacking ε T → T.card ≤ S.card)
  (hx : ‖x‖ ≤ 1) :
-- imply
  ∃ θ ∈ S, dist x θ ≤ 2 * ε := by
-- proof
  by_contra h
  push_neg at h
  have hxnotinS : x ∉ S := by
    intro hmem
    have := h x hmem
    simp [dist_self] at this
    linarith
  have hT_packing : IsEpsPacking ε (insert x S) := by
    constructor
    · intro z hz
      rw [Finset.mem_insert] at hz
      obtain rfl | hz := hz
      · exact hx
      · exact hS.1 z hz
    · intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      obtain rfl | ha <;> rcases hb with rfl | hb := ha
      · exact absurd rfl hab
      · exact le_of_lt (h b hb)
      · rw [dist_comm]; exact le_of_lt (h a ha)
      · exact hS.2 a ha b hb hab
  have hcard : (insert x S).card = S.card + 1 :=
    Finset.card_insert_of_notMem hxnotinS
  have := hMax _ hT_packing
  omega

end Chapter5.Problem53

namespace Chapter5.Problem53

/--
[problem_5_3c](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Problem_5_3.lean)
-/
@[path]
lemma problem_5_3c
  {d : ℕ}
  {ε : ℝ}
  {S : Finset (EuclideanSpace ℝ (Fin d))}
-- given
  (hd : 0 < d)
  (hε : 0 < ε)
  (hε1 : ε ≤ 1 / 2)
  (hS : IsEpsPacking ε S)
  (hMax : ∀ T : Finset (EuclideanSpace ℝ (Fin d)), IsEpsPacking ε T → T.card ≤ S.card) :
-- imply
  ∃ C' : ℝ, 0 < C' ∧ (S.card : ℝ) ≥ C' / ε ^ d := by
-- proof
  refine ⟨ε ^ d, pow_pos hε d, ?_⟩
  rw [div_self (ne_of_gt (pow_pos hε d))]
  have h0 : IsEpsPacking ε ({0} : Finset (EuclideanSpace ℝ (Fin d))) := by
    constructor
    · intro x hx; rw [Finset.mem_singleton] at hx; subst hx; simp
    · intro x hx y hy hne
      rw [Finset.mem_singleton] at hx hy
      subst hx; subst hy; exact absurd rfl hne
  have hcard : 1 ≤ S.card := by
    have := hMax _ h0
    simp at this
    exact Finset.Nonempty.card_pos this
  exact_mod_cast hcard
end



-- created on 2026-10-23
