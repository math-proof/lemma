/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part3
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneP2CoordinateToggleObstruction

open FluxEdgeCopy

variable {D : Type*}


@[simp] theorem BondwiseSuffixSpec.toRunSpec_event
    (E : BondwiseSuffixSpec V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) :
    E.toRunSpec.Event G m <-> E.Event G m := by
  cases E
  simp [BondwiseRunSpec.Event, BondwiseRunSpec.TerminalEvent,
    BondwiseSuffixSpec.Event, BondwiseSuffixSpec.toRunSpec]


end BackboneConcreteSelector
end
end StatMech.Sharpness
