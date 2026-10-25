/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part7
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

noncomputable def fin3PathDomain : shb_ExplorationDomain (Fin 3) where
  graph := fin3PathGraph
  active :=
    {canonicalEdgeSegment fin3PathGraph fin3LeftEdge,
      canonicalEdgeSegment fin3PathGraph fin3RightEdge}
  active_supported := by
    intro seg hseg edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseg
    rcases hseg with rfl | rfl
    · change edge ∈
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge).edgeSet at hedge
      rw [canonicalEdgeSegment_edgeSet] at hedge
      simp only [Set.mem_singleton_iff] at hedge
      subst edge
      exact SimpleGraph.mem_edgeFinset.mp fin3LeftEdge.2
    · change edge ∈
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge).edgeSet at hedge
      rw [canonicalEdgeSegment_edgeSet] at hedge
      simp only [Set.mem_singleton_iff] at hedge
      subst edge
      exact SimpleGraph.mem_edgeFinset.mp fin3RightEdge.2

end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
