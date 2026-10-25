/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part6
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

@[simp] theorem fin3PathGraph_edgeFinset :
    fin3PathGraph.edgeFinset =
      {s((0 : Fin 3), 1), s((1 : Fin 3), 2)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, fin3PathGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    rcases he with rfl | rfl <;> decide


end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
