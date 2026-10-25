/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Walls.rc_downcompfibers
open Finset
open scoped NNReal FinsetFamily


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] in
@[simp] lemma raiseCoord_self (i : E) (ω : ConfigSpace E) : raiseCoord i ω i = true := by
  simp [raiseCoord]

omit [Fintype E] in
lemma raiseCoord_of_ne {i j : E} (h : j ≠ i) (ω : ConfigSpace E) :
    raiseCoord i ω j = ω j := by simp [raiseCoord, Function.update_of_ne h]


lemma cfgSupport_raiseCoord (i : E) (ω : ConfigSpace E) :
    cfgSupport (raiseCoord i ω) = insert i (cfgSupport ω) := by
  ext j
  simp only [mem_cfgSupport, raiseCoord, Function.update, Finset.mem_insert, mem_cfgSupport]
  by_cases h : j = i
  · subst h; simp
  · simp [h]


lemma mem_image_cfgSupport_iff (𝒜 : Finset (ConfigSpace E)) (ω : ConfigSpace E) :
    cfgSupport ω ∈ 𝒜.image cfgSupport ↔ ω ∈ 𝒜 := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨ω', hω', heq⟩
    have hωeq : ω' = ω := by
      have := congrArg supportCfg heq
      rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
    rwa [hωeq] at hω'
  · intro hω; exact ⟨ω, hω, rfl⟩


theorem rc_memberFiber_to_inter (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∧ (ω ∈ 𝒜) := by
  have hi : i ∉ cfgSupport ω := by simp [mem_cfgSupport, hω]
  rw [mem_downCompress, cfgSupport_raiseCoord,
    memberFiber_to_inter i (𝒜.image cfgSupport) hi,
    ← cfgSupport_raiseCoord, mem_image_cfgSupport_iff, mem_image_cfgSupport_iff]


theorem rc_nonMemberFiber_to_union (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∨ (ω ∈ 𝒜) := by
  have hi : i ∉ cfgSupport ω := by simp [mem_cfgSupport, hω]
  rw [mem_downCompress, nonMemberFiber_to_union i (𝒜.image cfgSupport) hi,
    ← cfgSupport_raiseCoord, mem_image_cfgSupport_iff, mem_image_cfgSupport_iff]


theorem rc_downCompress_fibers (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    (raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∧ (ω ∈ 𝒜)) ∧
    (ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜) ∨ (ω ∈ 𝒜)) :=
  ⟨rc_memberFiber_to_inter i 𝒜 hω, rc_nonMemberFiber_to_union i 𝒜 hω⟩


end StatMech.Walls
