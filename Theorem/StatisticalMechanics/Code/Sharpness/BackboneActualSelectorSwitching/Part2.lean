/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_summable_explorationFiberIndicator
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V)
    (P : (d.graph.edgeFinset -> Nat) -> Prop) [DecidablePred P] :
    Summable (fun m => if P m then
      shb_explorationCoordinateWeight beta J d m else 0) := by
  let f := fun m : d.graph.edgeFinset -> Nat =>
    shb_explorationCoordinateWeight beta J d m
  have hf : Summable f := shb_summable_weight d.graph beta J
  have heq : (fun m => if P m then f m else 0) =
      Set.indicator {m | P m} f := by
    funext m
    by_cases hm : P m <;> simp [Set.indicator, hm]
  rw [heq]
  exact hf.indicator _


theorem shb_activeSegmentFiberMass_eq_segmentNum
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) :
    (∑' m : d.graph.edgeFinset -> Nat,
      if shb_ActiveSegmentFiber d s hs m then
        shb_explorationCoordinateWeight beta J d m else 0) =
      shb_segmentNum beta J d s := by
  unfold shb_segmentNum
  rw [dif_pos hs]
  unfold shb_backboneNumSupport shb_ActiveSegmentFiber
    shb_explorationCoordinateWeight
  apply tsum_congr
  intro m
  by_cases h :
      sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1} /\
        shb_backboneSelectSupport d.graph (ofEdgeFun d.graph m) s.1 s.2.1 =
          some (s.toPath d.graph (d.active_supported s hs)) <;> simp [h]


end
end StatMech.Sharpness
