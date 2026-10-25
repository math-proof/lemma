/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorObstruction.Part3
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_singleEdge_rawSplit_zero_two {x y : V} (hxy : x ≠ y) :
    weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
        (ofEdgeFun (shb_singleEdgeGraph x y)
          (shb_singleEdgeConstantFlux x y 0)) *
      weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
        (ofEdgeFun (shb_singleEdgeGraph x y)
          (shb_singleEdgeConstantFlux x y 2)) = (1 / 2 : Real) := by
  have hadj : (shb_singleEdgeGraph x y).Adj x y := by
    rw [shb_singleEdgeGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_singleton _, hxy⟩
  unfold weight
  rw [shb_singleEdgeGraph_edgeFinset hxy]
  simp [ofEdgeFun, shb_singleEdgeConstantFlux, hadj]


theorem shb_singleEdge_rawSplit_one_one {x y : V} (hxy : x ≠ y) :
    weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
        (ofEdgeFun (shb_singleEdgeGraph x y)
          (shb_singleEdgeConstantFlux x y 1)) *
      weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
        (ofEdgeFun (shb_singleEdgeGraph x y)
          (shb_singleEdgeConstantFlux x y 1)) = (1 : Real) := by
  have hadj : (shb_singleEdgeGraph x y).Adj x y := by
    rw [shb_singleEdgeGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_singleton _, hxy⟩
  unfold weight
  rw [shb_singleEdgeGraph_edgeFinset hxy]
  simp [ofEdgeFun, shb_singleEdgeConstantFlux, hadj]


theorem shb_singleEdge_edgeCopyMultiplicity_two {x y : V} (hxy : x ≠ y) :
    2 *
        (weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph x y)
            (shb_singleEdgeConstantFlux x y 0)) *
        weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph x y)
            (shb_singleEdgeConstantFlux x y 2))) =
      weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph x y)
            (shb_singleEdgeConstantFlux x y 1)) *
        weight (shb_singleEdgeGraph x y) 1 (fun _ => 1)
          (ofEdgeFun (shb_singleEdgeGraph x y)
            (shb_singleEdgeConstantFlux x y 1)) := by
  rw [shb_singleEdge_rawSplit_zero_two hxy,
    shb_singleEdge_rawSplit_one_one hxy]
  norm_num

end
end StatMech.Sharpness
