/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Def.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

theorem canonicalEdgeSegment_edgeSet
    (G : SimpleGraph V)
    (e : G.edgeFinset) :
    (canonicalEdgeSegment G e).edgeSet = {e.1} := by
  simp only [canonicalEdgeSegment]
  ext f
  simp only [shb_AmbientSegment.edgeSet, Set.mem_setOf_eq,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
    List.mem_singleton, Set.mem_singleton_iff]
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
  rw [hout]


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
