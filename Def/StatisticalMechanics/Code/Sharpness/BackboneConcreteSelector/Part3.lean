/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
import Structure.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelector.Part3
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


noncomputable def BondwiseCoordinateCertificate.toCoordinateToggleData
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V)
    (suffix₁ suffix₂ : List (Sym2 V))
    (bit₁ bit₂ : Nat -> Bool)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (R : BondwiseCoordinateCertificate X x accepted suffix₁ suffix₂
      bit₁ bit₂ S beta J d s ss hs) :
    CoordinateToggleData S beta J d s ss hs where
  path := R.path
  path_sources := R.path_sources
  transport := by
    intro m hm T
    let Q : (d.graph.edgeFinset -> Nat) -> Prop :=
      BondwiseSuffixEvent d.graph X (X.advance x accepted) suffix₁ bit₁
    let U : (d.graph.edgeFinset -> Nat) -> Prop :=
      BondwiseSuffixEvent d.graph X (X.advance x accepted) suffix₂ bit₂
    have hQ : FluxEventOutsideCut d.graph m
        ((X.bondwiseOrdered.tests x).determinedCut accepted) Q :=
      bondwiseSuffixEvent_fluxEventOutsideCut d.graph X x accepted suffix₁
        R.fresh₁ bit₁ m
    have hU : FluxEventOutsideCut d.graph m
        ((X.bondwiseOrdered.tests x).determinedCut accepted) U :=
      bondwiseSuffixEvent_fluxEventOutsideCut d.graph X x accepted suffix₂
        R.fresh₂ bit₂ m
    exact (R.left_normal_form m hm T).trans
      ((pairTransport_of_fluxEventsOutsideCut d.graph m
        ((X.bondwiseOrdered.tests x).determinedCut accepted) Q U hQ hU
        (R.path m hm) (R.path_supported m hm) T).trans
          (R.right_normal_form m hm (T ∆ R.path m hm)).symm)

end BackboneConcreteSelector
end
end StatMech.Sharpness
