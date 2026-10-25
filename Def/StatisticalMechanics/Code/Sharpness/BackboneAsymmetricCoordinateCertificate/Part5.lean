/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part2
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


def BondwisePairEvent
    (E₁ E₂ : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat)
    (T : Finset (Copy G m)) : Prop :=
  E₁.Event G (profileFlux G m T) /\
    E₂.Event G (profileFlux G m (univ \ T))


def BondwiseRunToggleCovariance
    (E F : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) (path : Finset (Copy G m)) : Prop :=
  ∀ T, E.Event G (profileFlux G m T) <->
    F.Event G (profileFlux G m (T ∆ path))


end BackboneConcreteSelector
end
end StatMech.Sharpness
