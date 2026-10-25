/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

noncomputable def edgeOfSegment?
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    Option d.graph.edgeFinset :=
  if h : ∃ e : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e = s then
    some (Classical.choose h)
  else none

end BackboneConcreteBondProgram
end
end StatMech.Sharpness
