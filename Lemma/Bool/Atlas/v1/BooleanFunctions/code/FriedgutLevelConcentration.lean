import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Friedgut
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Friedgut
import Theorem.v1.Atlas.BooleanFunctions.code.UncoveredBatch2
open Finset Real


namespace BooleanFourier

/--
[friedgut_junta_corollary_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FriedgutLevelConcentration.lean)
-/
@[path]
lemma friedgut_junta_corollary_bound
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {K : ℝ}
-- given
  (hVar : varianceReal (liftPM f) > 0)
  (hK1 : K ≥ 1)
  (hIK : totalInfluence f ≤ K * varianceReal (liftPM f)) :
-- imply
  ∃ i : Fin n, influence f i ≥ Real.exp (-5 * K) := by
-- proof
  set τ := Real.exp (-5 * K)
  have hτ_pos : (0 : ℝ) < τ := Real.exp_pos _
  have hτ_lt_one : τ < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h_tight := friedgut_tight_concentration f τ hτ_pos hτ_lt_one
  have hlog_val : Real.log (1 / τ) = 5 * K := by
    have h1 : (1 : ℝ) / τ = Real.exp (5 * K) := by
      show 1 / Real.exp (-5 * K) = Real.exp (5 * K)
      rw [show (-5 : ℝ) * K = -(5 * K) from by ring, Real.exp_neg, one_div, inv_inv]
    rw [h1, Real.log_exp]
  rw [hlog_val] at h_tight
  have hK_pos : (0 : ℝ) < K := by linarith
  have h5K_pos : (0 : ℝ) < 5 * K := by linarith
  have h_tail_le : 2 * totalInfluence f / (5 * K) ≤ 2 * varianceReal (liftPM f) / 5 := by
    rw [div_le_div_iff₀ h5K_pos (by norm_num : (0:ℝ) < 5)]
    nlinarith
  by_contra h_none
  push Not at h_none
  have hJ_empty : highInfluenceCoords f τ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i
    simp only [highInfluenceCoords, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact h_none i
  have h_filter_eq : (univ : Finset (Finset (Fin n))).filter
    (fun S => ¬(S ⊆ highInfluenceCoords f τ)) =
    (univ : Finset (Finset (Fin n))).filter (· ≠ ∅) := by
    congr 1; ext S
    simp only [hJ_empty, Finset.subset_empty, ne_eq]
  rw [h_filter_eq] at h_tight
  have h_var_eq : ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (· ≠ ∅),
    fourierCoeff (liftPM f) S ^ 2 = varianceReal (liftPM f) := by
    unfold varianceReal
    rfl
  rw [h_var_eq] at h_tight
  have h_absurd : varianceReal (liftPM f) ≤ 2 * varianceReal (liftPM f) / 5 := by
    linarith
  linarith

end BooleanFourier

namespace BooleanFourier

/--
[friedgut_junta_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FriedgutLevelConcentration.lean)
-/
@[path]
lemma friedgut_junta_theorem
-- imply
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (K : ℝ), varianceReal (liftPM f) > 0 → K ≥ 1 → totalInfluence f ≤ K * varianceReal (liftPM f) → ∃ i : Fin n, influence f i ≥ Real.exp (-C * K) := by
-- proof
  refine ⟨5, by norm_num, fun n f K hVar hK1 hIK => ?_⟩
  exact friedgut_junta_corollary_bound f K hVar hK1 hIK

end BooleanFourier


-- created on 2026-10-23
