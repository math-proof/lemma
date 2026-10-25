/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondToggle

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneTwoEdgeBondProgram

open BackboneDeterminedCutSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

noncomputable def residualEdge
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f) :
    (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset :=
  ⟨f.1, secondEdge_mem_delete d e f hne⟩


end BackboneTwoEdgeBondToggle
end
end StatMech.Sharpness
