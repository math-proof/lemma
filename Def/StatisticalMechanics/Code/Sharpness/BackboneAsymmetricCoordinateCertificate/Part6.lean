/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Structure.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part3
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


noncomputable def AsymmetricBondwiseCoordinateCertificate.toCoordinateToggleData
    (left₁ left₂ right₁ right₂ : BondwiseRunSpec V)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (R : AsymmetricBondwiseCoordinateCertificate
      left₁ left₂ right₁ right₂ S beta J d s ss hs) :
    CoordinateToggleData S beta J d s ss hs where
  path := R.path
  path_sources := R.path_sources
  transport := by
    intro m hm T
    exact (R.left_normal_form m hm T).trans
      ((R.bondwise_toggle m hm T).trans
        (R.right_normal_form m hm (T ∆ R.path m hm)).symm)


end BackboneConcreteSelector
end
end StatMech.Sharpness
