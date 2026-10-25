/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part11
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


theorem CompleteBondwiseSelectorSpec.canonicalToggleExists_of_componentwise
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h : R.CanonicalComponentwiseToggleExists beta J d s ss hs) :
    R.CanonicalBondwiseToggleExists beta J d s ss hs := by
  intro m hm
  obtain ⟨path, hhead, hresidual⟩ := h m hm
  exact ⟨path, BondwisePairEvent.toggle_iff_of_componentwise
    (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
    (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
    d.graph m path hhead hresidual⟩


end BackboneConcreteSelector
end
end StatMech.Sharpness
