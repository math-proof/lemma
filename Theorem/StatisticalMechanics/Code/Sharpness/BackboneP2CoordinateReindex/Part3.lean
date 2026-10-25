/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateReindex.Part3
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneP2CoordinateReindex

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

variable {H G : SimpleGraph V}


theorem actualMass_active_of_coordinateToggle
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
      (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss))
    (path_sources : ∀ m hm,
      RandomCurrent.sources (FluxEdgeCopy.endsM d.graph m) (path m hm) =
        stepToggleSource S d s ss)
    (transport : ∀ m hm T,
      (S.Fiber d (s :: ss) (FluxEdgeCopy.profileFlux d.graph m T) ∧
          liftedResidualVacuum d s
            (FluxEdgeCopy.profileFlux d.graph m (univ \ T))) <->
        (shb_ActiveSegmentFiber d s hs
            (FluxEdgeCopy.profileFlux d.graph m (T ∆ path m hm)) ∧
          liftedResidualFiber S d s ss
            (FluxEdgeCopy.profileFlux d.graph m
              (univ \ (T ∆ path m hm))))) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  apply actualMass_active_of_contributingToggle S beta J d s ss
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
    ?_ ?_ path path_sources transport
  · exact partialActualMass_mul_residualCurrentSum_eq_pairTsum
      S beta J d s ss
  · simpa [stepToggleSource] using
      segmentNum_mul_partialActualMass_eq_pairTsum S beta J d s ss hs

end BackboneP2CoordinateReindex
end
end StatMech.Sharpness
