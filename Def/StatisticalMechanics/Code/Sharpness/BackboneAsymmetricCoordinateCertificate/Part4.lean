/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate
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


noncomputable def BondwiseRunSpec.ofPredicate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : (G.edgeFinset -> Nat) -> Prop) : BondwiseRunSpec V where
  State := Unit
  scan :=
    { edgeOrder := fun _ => []
      edgeOrder_nodup := by simp
      advance := fun _ _ => () }
  state := ()
  suffix := []
  bit := fun _ => false
  terminal := fun _ omega => Q (fun e => (omega e.1).getD 0)


end BackboneConcreteSelector
end
end StatMech.Sharpness
