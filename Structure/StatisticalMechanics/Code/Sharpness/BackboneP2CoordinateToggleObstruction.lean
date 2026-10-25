/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateToggleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateReindex.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneP2CoordinateToggleObstruction

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open FluxEdgeCopy


structure CoordinateToggleData
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) where
  path : ContributingPathSelector d.graph beta J
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
  path_sources : ∀ m hm,
    RandomCurrent.sources (endsM d.graph m) (path m hm) =
      stepToggleSource S d s ss
  transport : ∀ m hm T,
    (S.Fiber d (s :: ss) (profileFlux d.graph m T) ∧
        liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T))) <->
      (shb_ActiveSegmentFiber d s hs
          (profileFlux d.graph m (T ∆ path m hm)) ∧
        liftedResidualFiber S d s ss
          (profileFlux d.graph m (univ \ (T ∆ path m hm))))


end BackboneP2CoordinateToggleObstruction
end
end StatMech.Sharpness
