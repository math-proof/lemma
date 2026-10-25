/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Abbrev.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part3
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_LocalSelectorFiberCutResummation
    (β : ℝ) (J : Sym2 V → ℝ) (fiberMass : shb_ExplorationFiberMass V) : Prop := by
  classical
  exact (∀ d, fiberMass d [] = currentSum d.graph β J ∅) ∧
    (∀ d s ss, s ∈ d.active →
      fiberMass d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph β J ∅ =
        shb_segmentNum β J d s *
          fiberMass (shb_BackboneExplorationDomain.advance d s) ss) ∧
    (∀ d s ss, s ∉ d.active → fiberMass d (s :: ss) = 0)


noncomputable def shb_normalizedExplorationRho
    (β : ℝ) (J : Sym2 V → ℝ) (fiberMass : shb_ExplorationFiberMass V)
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V)) : ℝ :=
  fiberMass d word / currentSum d.graph β J ∅

end
end StatMech.Sharpness
