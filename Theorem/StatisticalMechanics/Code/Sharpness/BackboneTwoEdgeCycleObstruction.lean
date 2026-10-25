/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCycleObstruction

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open FluxEdgeCopy

@[simp] theorem graph_edgeFinset :
    graph.edgeFinset =
      {s((0 : Fin 6), 1), s((1 : Fin 6), 2), s((3 : Fin 6), 4),
        s((4 : Fin 6), 5), s((5 : Fin 6), 3)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, graph,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
