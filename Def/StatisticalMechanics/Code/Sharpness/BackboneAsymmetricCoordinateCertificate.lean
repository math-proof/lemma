/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Structure.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate
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


def BondwiseSuffixSpec.Event
    (E : BondwiseSuffixSpec V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) : Prop :=
  BondwiseSuffixEvent G E.scan E.state E.suffix E.bit m

end BackboneConcreteSelector
end
end StatMech.Sharpness
