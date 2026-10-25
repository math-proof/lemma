/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Def.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part3
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

theorem edgeOfSegment?_eq_some_spec
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (e : d.graph.edgeFinset)
    (h : edgeOfSegment? d s = some e) :
    canonicalEdgeSegment d.graph e = s := by
  unfold edgeOfSegment? at h
  split at h
  · rename_i hex
    have he : Classical.choose hex = e := Option.some.inj h
    simpa [he] using Classical.choose_spec hex
  · simp at h


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
