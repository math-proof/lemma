/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.KestenThresholdRoute
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace TwoDim

open ConfigSpace Function Finset StatMech StatMech.Sharpness StatMech.BeffaraDC
  StatMech.Probability StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [DecidableEq E] in


theorem kklw_weight_eq (p : ℝ) (ω : ConfigSpace E) :
    OSSS.weight (OSSS.bernoulliWeight p) ω = StatMech.configWeight p ω := by
  unfold OSSS.weight OSSS.bernoulliWeight StatMech.configWeight StatMech.edgeWeight
  rfl


theorem kklw_prob_eq_expect (p : ℝ) (A : Set (ConfigSpace E)) :
    StatMech.prob p A
      = OSSS.expect (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) := by
  unfold StatMech.prob OSSS.expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [kklw_weight_eq]; ring


theorem kklw_influence_eq_infl (p : ℝ) (A : Set (ConfigSpace E)) (e : E) :
    StatMech.BeffaraDC.influence p A e
      = OSSS.infl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) e := by
  unfold StatMech.BeffaraDC.influence StatMech.pivotalProb
  rw [OSSS.infl_indicator_eq_pivotal]
  unfold OSSS.expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [kklw_weight_eq]; ring


theorem kklw_sum_influence_eq_totalInfl (p : ℝ) (A : Set (ConfigSpace E)) :
    ∑ e, StatMech.BeffaraDC.influence p A e
      = totalInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) := by
  unfold totalInfl
  exact Finset.sum_congr rfl (fun e _ => kklw_influence_eq_infl p A e)

omit [Fintype E] [DecidableEq E] in


theorem kklw_decide_eq_indicator (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] :
    (fun ω => if (decide (ω ∈ A)) then (1:ℝ) else 0) = A.indicator (fun _ => (1:ℝ)) := by
  funext ω; rw [Set.indicator_apply]; by_cases h : ω ∈ A <;> simp [h]


theorem kklw_var_eq (p : ℝ) (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] :
    OSSS.var (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ)))
      = StatMech.prob p A * (1 - StatMech.prob p A) := by
  rw [← kklw_decide_eq_indicator A, kkl_var_indicator_eq]
  rw [kklw_decide_eq_indicator A, ← kklw_prob_eq_expect]


end TwoDim
end StatMech
