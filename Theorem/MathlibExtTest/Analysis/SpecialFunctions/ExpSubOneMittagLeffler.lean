/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ExpSubOneMittagLeffler.lean -/


import Def.Analysis.SpecialFunctions.ExpSubOneMittagLeffler
import Lemma.Real.ExpSubOneMittagLeffler
import Mathlib.Tactic


namespace MathlibExtTest.Analysis.SpecialFunctions.ExpSubOneMittagLeffler

open Asymptotics Filter

open MetaMathlibExt

open scoped Topology

noncomputable section

-- At `u = 1`, the Mittag-Leffler terms give a concrete lower bound.
example : (1 : ℝ) / 2 ≤ 1 / (Real.exp 1 - 1) := by
  rw [one_div_exp_sub_one_eq_tsum 1 (by norm_num)]
  have hsum : 0 ≤
      ∑' m : ℕ, 2 / (1 + 4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) :=
    tsum_nonneg fun _ ↦ by positivity
  norm_num
  exact hsum

-- At `u = -1`, the negative Mittag-Leffler terms give a concrete upper bound.
example : 1 / (Real.exp (-1) - 1) ≤ (-3 : ℝ) / 2 := by
  rw [one_div_exp_sub_one_eq_tsum (-1) (by norm_num)]
  have hsum :
      (∑' m : ℕ,
          (-2 : ℝ) / (1 + 4 * Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2)) ≤ 0 :=
    tsum_nonpos fun _ ↦
      div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  norm_num
  exact hsum

-- The first Laurent truncation has a cubic remainder at the origin.
example :
    (fun v : ℝ => 1 / (Real.exp v - 1) - 1 / v + 1 / 2 - v / 12) =O[𝓝[≠] 0]
      (fun v : ℝ => |v| ^ 3) := by
  obtain ⟨C, _, hbound⟩ := abs_one_div_exp_sub_one_sub_laurent_le 1
  refine IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have h := hbound v hv
  norm_num [Finset.sum_range_succ, bernoulli_two] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_abs]
  convert h using 1
  ring_nf

-- The analytic cubic remainder and its derivative both vanish at the origin.
example : oneDivExpSubOneLaurentRemainder 1 0 = 0 ∧
    HasDerivAt (oneDivExpSubOneLaurentRemainder 1) 0 0 := by
  have hvalue := oneDivExpSubOneLaurentRemainder_abs_le 1 0
  have hderiv := abs_deriv_oneDivExpSubOneLaurentRemainder_le 1 0
  norm_num at hvalue hderiv
  constructor
  · exact hvalue
  · have hd : HasDerivAt (oneDivExpSubOneLaurentRemainder 1)
        (deriv (oneDivExpSubOneLaurentRemainder 1) 0) 0 :=
      (differentiable_oneDivExpSubOneLaurentRemainder 1).differentiableAt.hasDerivAt
    simpa only [hderiv] using hd

end
end MathlibExtTest.Analysis.SpecialFunctions.ExpSubOneMittagLeffler
