/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
import Abbrev.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelector
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


structure BondwiseCoordinateCertificate
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V)
    (suffix₁ suffix₂ : List (Sym2 V))
    (bit₁ bit₂ : Nat -> Bool)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) where
  fresh₁ : SuffixFresh X x accepted suffix₁
  fresh₂ : SuffixFresh X x accepted suffix₂
  path : ContributingPathSelector d.graph beta J
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
  path_sources : ∀ m hm,
    RandomCurrent.sources (endsM d.graph m) (path m hm) =
      stepToggleSource S d s ss
  path_supported : ∀ m hm,
    SupportedInCut d.graph m
      ((X.bondwiseOrdered.tests x).determinedCut accepted) (path m hm)
  left_normal_form : ∀ m
      (_hm : CoordinatePairContributes S beta J d s ss hs m) T,
    (S.Fiber d (s :: ss) (profileFlux d.graph m T) ∧
        liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T))) ↔
      (BondwiseSuffixEvent d.graph X (X.advance x accepted)
          suffix₁ bit₁ (profileFlux d.graph m T) ∧
        BondwiseSuffixEvent d.graph X (X.advance x accepted)
          suffix₂ bit₂ (profileFlux d.graph m (univ \ T)))
  right_normal_form : ∀ m
      (_hm : CoordinatePairContributes S beta J d s ss hs m) T,
    (shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) ∧
        liftedResidualFiber S d s ss
          (profileFlux d.graph m (univ \ T))) ↔
      (BondwiseSuffixEvent d.graph X (X.advance x accepted)
          suffix₁ bit₁ (profileFlux d.graph m T) ∧
        BondwiseSuffixEvent d.graph X (X.advance x accepted)
          suffix₂ bit₂ (profileFlux d.graph m (univ \ T)))


end BackboneConcreteSelector
end
end StatMech.Sharpness
