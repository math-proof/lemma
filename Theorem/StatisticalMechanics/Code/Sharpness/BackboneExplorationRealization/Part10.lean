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
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part11
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_normalizedExplorationRho_nil
    (β : ℝ) (J : Sym2 V → ℝ) (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass)
    (d : shb_ExplorationDomain V) :
    shb_normalizedExplorationRho β J fiberMass d [] = 1 := by
  letI : DecidableRel d.graph.Adj := Classical.decRel _
  rw [shb_normalizedExplorationRho, hcut.1 d]
  exact div_self (ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos d.graph β J))


theorem shb_normalizedExplorationRho_cons
    (β : ℝ) (J : Sym2 V → ℝ) (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) :
    shb_normalizedExplorationRho β J fiberMass d (s :: ss) =
      shb_BackboneExplorationDomain.amplitude β J d s *
        shb_normalizedExplorationRho β J fiberMass
          (shb_BackboneExplorationDomain.advance d s) ss := by
  let d' := shb_BackboneExplorationDomain.advance d s
  letI : DecidableRel d.graph.Adj := Classical.decRel _
  letI : DecidableRel d'.graph.Adj := Classical.decRel _
  by_cases hs : s ∈ d.active
  · have hZd : currentSum d.graph β J ∅ ≠ 0 :=
      ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos d.graph β J)
    have hZd' : currentSum d'.graph β J ∅ ≠ 0 :=
      ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos d'.graph β J)
    rw [shb_normalizedExplorationRho, shb_normalizedExplorationRho,
      shb_segmentRho_eq_num_div]
    field_simp [hZd]
    exact (eq_div_iff hZd').2 (hcut.2.1 d s ss hs)
  · rw [shb_normalizedExplorationRho, hcut.2.2 d s ss hs]
    simp [shb_BackboneExplorationDomain.amplitude, hs]


theorem shb_randomCurrent_rho_eq_weight
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation β J)
    (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass)
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V)) :
    shb_normalizedExplorationRho β J fiberMass d word =
      (shb_BackboneExplorationDomain.kernel β J hβ hJ hdom).weight d word := by
  induction word generalizing d with
  | nil =>
      rw [shb_normalizedExplorationRho_nil β J fiberMass hcut]
      rfl
  | cons s ss ih =>
      rw [shb_normalizedExplorationRho_cons β J fiberMass hcut,
        shb_ExplorationKernel.weight_cons, ih]
      rfl


end
end StatMech.Sharpness
