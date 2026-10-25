/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Def.StatisticalMechanics.Code.OSSS.StepCov.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace StepCov

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg OSSS.LindebergTree

open OSSS.DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


namespace Counterexample

lemma muU_pos : ∀ ω, 0 < muU ω := fun _ => by unfold muU; norm_num

lemma muU_sum_one : ∑ ω : ConfigSpace Bool, muU ω = 1 := by
  unfold muU; rw [sum_boolfun]; norm_num

lemma mean_fAvg : mean muU fAvg = 1 / 2 := by
  unfold mean muU fAvg; rw [sum_boolfun]; norm_num

lemma cov_fAvg : Lindeberg.cov muU fAvg (coord false) = 1 / 8 := by
  unfold Lindeberg.cov Lindeberg.mean muU fAvg coord
  rw [sum_boolfun, sum_boolfun, sum_boolfun]; norm_num

lemma condNorm_false : condNorm muU {false} (fun _ => false) = 1 / 2 := by
  unfold condNorm muU Agree; rw [sum_boolfun]; norm_num [Finset.mem_singleton]

lemma condNorm_true : condNorm muU {false} (fun _ => true) = 1 / 2 := by
  unfold condNorm muU Agree; rw [sum_boolfun]; norm_num [Finset.mem_singleton]

lemma cExp_false : cExp muU {false} fAvg (fun _ => false) = 1 / 4 := by
  rw [cExp_eq_cSum_div, condNorm_false]
  unfold cSum muU fAvg Agree; rw [sum_boolfun]; norm_num [Finset.mem_singleton]

lemma cExp_true : cExp muU {false} fAvg (fun _ => true) = 3 / 4 := by
  rw [cExp_eq_cSum_div, condNorm_true]
  unfold cSum muU fAvg Agree; rw [sum_boolfun]; norm_num [Finset.mem_singleton]


lemma pathPrefix_Tw_one (ω : ConfigSpace Bool) : pathPrefix Tw ω 1 = {false} := by
  unfold Tw; rw [pathPrefix_node_succ, pathPrefix_zero]; simp


lemma freshAt_Tw_zero (ω : ConfigSpace Bool) : freshAt Tw ω 0 false = 1 := by
  unfold freshAt; rw [pathPrefix_zero, pathPrefix_Tw_one]; simp


lemma cExp_false_branch (ω : ConfigSpace Bool) :
    cExp muU {false} fAvg ω = if ω false then (3:ℝ)/4 else 1/4 := by
  have hfm := cExp_Fmeas muU {false} fAvg
  by_cases hb : ω false
  · rw [if_pos hb]
    rw [← cExp_true]; apply hfm
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx; rw [hb]
  · rw [if_neg hb]
    rw [← cExp_false]; apply hfm
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    simp only [Bool.not_eq_true] at hb; rw [hb]


lemma mean_step_witness :
    mean muU (fun ω => |adaptM muU Tw fAvg (0 + 1) ω - adaptM muU Tw fAvg 0 ω|
        * freshAt Tw ω 0 false) = 1 / 4 := by
  have hadapt0 : ∀ ω, adaptM muU Tw fAvg 0 ω = 1 / 2 := by
    intro ω; rw [adaptM, pathPrefix_zero, cExp_empty muU_sum_one, mean_fAvg]
  have hadapt1 : ∀ ω, adaptM muU Tw fAvg (0 + 1) ω = if ω false then (3:ℝ)/4 else 1/4 := by
    intro ω; rw [adaptM, pathPrefix_Tw_one, cExp_false_branch]
  have hpt : ∀ ω, |adaptM muU Tw fAvg (0 + 1) ω - adaptM muU Tw fAvg 0 ω|
      * freshAt Tw ω 0 false = 1 / 4 := by
    intro ω
    rw [hadapt0, hadapt1, freshAt_Tw_zero, mul_one]
    by_cases hb : ω false
    · rw [if_pos hb]; rw [show (3:ℝ)/4 - 1/2 = 1/4 from by norm_num, abs_of_pos (by norm_num)]
    · rw [if_neg hb]; rw [show (1:ℝ)/4 - 1/2 = -(1/4) from by norm_num, abs_neg,
        abs_of_pos (by norm_num)]
  unfold mean
  rw [show (fun ω => (fun ω => |adaptM muU Tw fAvg (0 + 1) ω - adaptM muU Tw fAvg 0 ω|
      * freshAt Tw ω 0 false) ω * muU ω) = (fun ω => (1:ℝ)/4 * muU ω) from by
        funext ω; simp only []; rw [hpt ω]]
  rw [← Finset.mul_sum, muU_sum_one, mul_one]


theorem stepCovBound_no_factor_false :
    ¬ LindebergTree.StepCovBound muU Tw fAvg := by
  intro hSCB
  have h := hSCB 0 false
  rw [mean_step_witness] at h
  
  have hrhs : Lindeberg.cov muU fAvg (coord false)
      * mean muU (fun ω => freshAt Tw ω 0 false) = 1 / 8 := by
    rw [cov_fAvg]
    have hfresh : mean muU (fun ω => freshAt Tw ω 0 false) = 1 := by
      unfold mean
      rw [show (fun ω => (fun ω => freshAt Tw ω 0 false) ω * muU ω)
            = (fun ω => (1:ℝ) * muU ω) from by funext ω; simp only []; rw [freshAt_Tw_zero]]
      rw [← Finset.mul_sum, muU_sum_one, mul_one]
    rw [hfresh, mul_one]
  rw [hrhs] at h
  norm_num at h

end Counterexample
end StepCov
end OSSS
end StatMech
