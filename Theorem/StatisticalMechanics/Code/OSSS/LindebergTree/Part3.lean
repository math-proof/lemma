/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Def.StatisticalMechanics.Code.OSSS.LindebergTree.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace LindebergTree

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg

open OSSS.DecisionTree

section Analytic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma adaptM_zero {μ : ConfigSpace E → ℝ} (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    adaptM μ T f 0 ω = mean μ f := by
  unfold adaptM
  rw [pathPrefix_zero]
  exact cExp_empty hμ1 f ω


lemma cExp_queried_evalR {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (ω : ConfigSpace E) :
    cExp μ (T.queried ω) (T.evalR) ω = T.evalR ω := by
  unfold cExp condMass
  have hZ : 0 < condNorm μ (T.queried ω) ω := condNorm_pos hpos _ _
  
  have hval : ∀ ω', Agree (T.queried ω) ω ω' →
      T.evalR ω' = T.evalR ω := by
    intro ω' hag
    unfold DecisionTree.evalR
    rw [Coding.eval_eq_of_agree_on_queried T ω ω' (fun e he => hag e he)]
  calc ∑ ω', T.evalR ω' * ((if Agree (T.queried ω) ω ω' then μ ω' else 0) / condNorm μ (T.queried ω) ω)
      = ∑ ω', T.evalR ω * ((if Agree (T.queried ω) ω ω' then μ ω' else 0) / condNorm μ (T.queried ω) ω) := by
        apply Finset.sum_congr rfl
        intro ω' _
        by_cases hag : Agree (T.queried ω) ω ω'
        · rw [if_pos hag, hval ω' hag]
        · rw [if_neg hag]; simp
    _ = T.evalR ω * ∑ ω', ((if Agree (T.queried ω) ω ω' then μ ω' else 0) / condNorm μ (T.queried ω) ω) := by
        rw [Finset.mul_sum]
    _ = T.evalR ω := by
        rw [← Finset.sum_div]
        have : (∑ ω', if Agree (T.queried ω) ω ω' then μ ω' else 0) = condNorm μ (T.queried ω) ω := rfl
        rw [this, div_self hZ.ne', mul_one]


lemma adaptM_depth {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (T : DecisionTree E)
    (ω : ConfigSpace E) :
    adaptM μ T (T.evalR) (treeDepth T) ω = T.evalR ω := by
  unfold adaptM
  rw [pathPrefix_depth_eq_queried]
  exact cExp_queried_evalR hpos T ω


lemma evalR_sub_mean_eq_sum {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) (ω : ConfigSpace E) :
    T.evalR ω - mean μ (T.evalR)
      = ∑ t ∈ Finset.range (treeDepth T),
          (adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
  rw [Finset.sum_range_sub (fun t => adaptM μ T (T.evalR) t ω) (treeDepth T)]
  rw [adaptM_depth hpos T ω, adaptM_zero hμ1 T (T.evalR) ω]


end Analytic
end LindebergTree
end OSSS
end StatMech
