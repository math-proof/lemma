/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part4
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


theorem edge_cases (e : domain.graph.edgeFinset) :
    e = headEdge ∨ e = suffixEdge ∨ e = cycleEdge₀ ∨
      e = cycleEdge₁ ∨ e = cycleEdge₂ := by
  have he : e.1 ∈ graph.edgeFinset := by
    simpa only [domain_graph] using e.2
  rw [graph_edgeFinset] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with he | he | he | he | he
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr (Or.inl (Subtype.ext he))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext he)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext he))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext he))))

@[simp] theorem superposition_head : superposition headEdge = 1 := by
  change (((((if headEdge = headEdge then 1 else 0) +
    (if headEdge = suffixEdge then 1 else 0)) +
    2 * (if headEdge = cycleEdge₀ then 1 else 0)) +
    2 * (if headEdge = cycleEdge₁ then 1 else 0)) +
    2 * (if headEdge = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem superposition_suffix : superposition suffixEdge = 1 := by
  change (((((if suffixEdge = headEdge then 1 else 0) +
    (if suffixEdge = suffixEdge then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₀ then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₁ then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem superposition_cycle₀ : superposition cycleEdge₀ = 2 := by
  change (((((if cycleEdge₀ = headEdge then 1 else 0) +
    (if cycleEdge₀ = suffixEdge then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem superposition_cycle₁ : superposition cycleEdge₁ = 2 := by
  change (((((if cycleEdge₁ = headEdge then 1 else 0) +
    (if cycleEdge₁ = suffixEdge then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem superposition_cycle₂ : superposition cycleEdge₂ = 2 := by
  change (((((if cycleEdge₂ = headEdge then 1 else 0) +
    (if cycleEdge₂ = suffixEdge then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem oddCycleFlux_head : oddCycleFlux headEdge = 0 := by
  change ((if headEdge = cycleEdge₀ then 1 else 0) +
    (if headEdge = cycleEdge₁ then 1 else 0) +
    (if headEdge = cycleEdge₂ then 1 else 0)) = 0
  simp

@[simp] theorem oddCycleFlux_suffix : oddCycleFlux suffixEdge = 0 := by
  change ((if suffixEdge = cycleEdge₀ then 1 else 0) +
    (if suffixEdge = cycleEdge₁ then 1 else 0) +
    (if suffixEdge = cycleEdge₂ then 1 else 0)) = 0
  simp

@[simp] theorem oddCycleFlux_cycle₀ : oddCycleFlux cycleEdge₀ = 1 := by
  change ((if cycleEdge₀ = cycleEdge₀ then 1 else 0) +
    (if cycleEdge₀ = cycleEdge₁ then 1 else 0) +
    (if cycleEdge₀ = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem oddCycleFlux_cycle₁ : oddCycleFlux cycleEdge₁ = 1 := by
  change ((if cycleEdge₁ = cycleEdge₀ then 1 else 0) +
    (if cycleEdge₁ = cycleEdge₁ then 1 else 0) +
    (if cycleEdge₁ = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem oddCycleFlux_cycle₂ : oddCycleFlux cycleEdge₂ = 1 := by
  change ((if cycleEdge₂ = cycleEdge₀ then 1 else 0) +
    (if cycleEdge₂ = cycleEdge₁ then 1 else 0) +
    (if cycleEdge₂ = cycleEdge₂ then 1 else 0)) = 1
  simp

theorem unitHead_le_superposition :
    unitFlux domain.graph headEdge ≤ superposition := by
  intro e
  have hu : unitFlux domain.graph headEdge e ≤ 1 := by
    change (if e = headEdge then 1 else 0) ≤ 1
    split <;> omega
  rcases edge_cases e with rfl | rfl | rfl | rfl | rfl <;>
    simp only [superposition_head, superposition_suffix,
      superposition_cycle₀, superposition_cycle₁, superposition_cycle₂] <;>
    omega

theorem oddCycleFlux_le_superposition : oddCycleFlux ≤ superposition := by
  intro e
  rcases edge_cases e with rfl | rfl | rfl | rfl | rfl <;> simp


end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
