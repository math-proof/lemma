/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part4
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


@[simp] theorem BondwiseRunSpec.ofPredicate_event
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : (G.edgeFinset -> Nat) -> Prop)
    (m : G.edgeFinset -> Nat) :
    (BondwiseRunSpec.ofPredicate G Q).Event G m <-> Q m := by
  have hread :
      (fun e : G.edgeFinset => (fluxOptionConfig G m e.1).getD 0) = m := by
    funext e
    simp [fluxOptionConfig, e.2]
  simp [BondwiseRunSpec.ofPredicate, BondwiseRunSpec.Event,
    BondwiseRunSpec.TerminalEvent, BondwiseSuffixEvent, hread]


end BackboneConcreteSelector
end
end StatMech.Sharpness
