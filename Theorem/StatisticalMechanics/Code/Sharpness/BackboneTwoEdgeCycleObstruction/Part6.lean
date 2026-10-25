/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part6
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCycleObstruction

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open FluxEdgeCopy

attribute [simp] headEdge_ne_suffixEdge headEdge_ne_cycleEdge₀
  headEdge_ne_cycleEdge₁ headEdge_ne_cycleEdge₂
  suffixEdge_ne_cycleEdge₀ suffixEdge_ne_cycleEdge₁
  suffixEdge_ne_cycleEdge₂ cycleEdge₀_ne_cycleEdge₁
  cycleEdge₀_ne_cycleEdge₂ cycleEdge₁_ne_cycleEdge₂
  suffixEdge_ne_headEdge cycleEdge₀_ne_headEdge cycleEdge₁_ne_headEdge
  cycleEdge₂_ne_headEdge cycleEdge₀_ne_suffixEdge
  cycleEdge₁_ne_suffixEdge cycleEdge₂_ne_suffixEdge
  cycleEdge₁_ne_cycleEdge₀ cycleEdge₂_ne_cycleEdge₀
  cycleEdge₂_ne_cycleEdge₁


@[simp] theorem suffixEvenFlux_head : suffixEvenFlux headEdge = 0 := by
  change ((((if headEdge = suffixEdge then 1 else 0) +
    2 * (if headEdge = cycleEdge₀ then 1 else 0)) +
    2 * (if headEdge = cycleEdge₁ then 1 else 0)) +
    2 * (if headEdge = cycleEdge₂ then 1 else 0)) = 0
  simp

@[simp] theorem suffixEvenFlux_suffix : suffixEvenFlux suffixEdge = 1 := by
  change ((((if suffixEdge = suffixEdge then 1 else 0) +
    2 * (if suffixEdge = cycleEdge₀ then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₁ then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem suffixEvenFlux_cycle₀ : suffixEvenFlux cycleEdge₀ = 2 := by
  change ((((if cycleEdge₀ = suffixEdge then 1 else 0) +
    2 * (if cycleEdge₀ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem suffixEvenFlux_cycle₁ : suffixEvenFlux cycleEdge₁ = 2 := by
  change ((((if cycleEdge₁ = suffixEdge then 1 else 0) +
    2 * (if cycleEdge₁ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem suffixEvenFlux_cycle₂ : suffixEvenFlux cycleEdge₂ = 2 := by
  change ((((if cycleEdge₂ = suffixEdge then 1 else 0) +
    2 * (if cycleEdge₂ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem unitHead_head :
    unitFlux domain.graph headEdge headEdge = 1 := by
  change (if headEdge = headEdge then 1 else 0) = 1
  simp

@[simp] theorem unitHead_suffix :
    unitFlux domain.graph headEdge suffixEdge = 0 := by
  change (if suffixEdge = headEdge then 1 else 0) = 0
  simp

@[simp] theorem unitHead_cycle₀ :
    unitFlux domain.graph headEdge cycleEdge₀ = 0 := by
  change (if cycleEdge₀ = headEdge then 1 else 0) = 0
  simp

@[simp] theorem unitHead_cycle₁ :
    unitFlux domain.graph headEdge cycleEdge₁ = 0 := by
  change (if cycleEdge₁ = headEdge then 1 else 0) = 0
  simp

@[simp] theorem unitHead_cycle₂ :
    unitFlux domain.graph headEdge cycleEdge₂ = 0 := by
  change (if cycleEdge₂ = headEdge then 1 else 0) = 0
  simp

theorem superposition_sub_unitHead :
    (fun e => superposition e - unitFlux domain.graph headEdge e) =
      suffixEvenFlux := by
  funext e
  rcases edge_cases e with rfl | rfl | rfl | rfl | rfl <;>
    simp only [superposition_head, superposition_suffix,
      superposition_cycle₀, superposition_cycle₁, superposition_cycle₂,
      suffixEvenFlux_head, suffixEvenFlux_suffix, suffixEvenFlux_cycle₀,
      suffixEvenFlux_cycle₁, suffixEvenFlux_cycle₂,
      unitHead_head, unitHead_suffix, unitHead_cycle₀, unitHead_cycle₁,
      unitHead_cycle₂]

@[simp] theorem profileFlux_headSplit_compl :
    profileFlux domain.graph superposition (univ \ headSplit) =
      suffixEvenFlux := by
  rw [profileFlux_compl, profileFlux_headSplit,
    superposition_sub_unitHead]


end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
