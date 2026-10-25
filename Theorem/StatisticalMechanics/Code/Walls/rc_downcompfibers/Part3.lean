/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_downcompfibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Walls.rc_downcompfibers.Part2
open Finset
open scoped NNReal FinsetFamily


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem rc_downCompress_fiber_count (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    ind (raiseCoord i ω ∈ downCompress i 𝒜) + ind (ω ∈ downCompress i 𝒜)
      = ind (raiseCoord i ω ∈ 𝒜) + ind (ω ∈ 𝒜) := by
  classical
  simp only [ind]
  rw [if_congr (rc_memberFiber_to_inter i 𝒜 hω) rfl rfl,
    if_congr (rc_nonMemberFiber_to_union i 𝒜 hω) rfl rfl]
  by_cases hm : raiseCoord i ω ∈ 𝒜 <;> by_cases hn : ω ∈ 𝒜 <;>
    simp [hm, hn]


theorem rc_fiber_univ_high (i : E) {ω : ConfigSpace E} (hω : ω i = false) :
    raiseCoord i ω ∈ downCompress i (Finset.univ : Finset (ConfigSpace E)) := by
  rw [rc_memberFiber_to_inter i _ hω]
  exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩


theorem rc_fiber_empty_low (i : E) {ω : ConfigSpace E} (hω : ω i = false) :
    ω ∉ downCompress i (∅ : Finset (ConfigSpace E)) := by
  rw [rc_nonMemberFiber_to_union i _ hω]
  rintro (h | h) <;> exact absurd h (Finset.notMem_empty _)


theorem rc_fiber_cases (i : E) (𝒜 : Finset (ConfigSpace E)) {ω : ConfigSpace E}
    (hω : ω i = false) :
    (raiseCoord i ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜 ∧ ω ∈ 𝒜)) ∧
    (ω ∈ downCompress i 𝒜 ↔ (raiseCoord i ω ∈ 𝒜 ∨ ω ∈ 𝒜)) :=
  rc_downCompress_fibers i 𝒜 hω

end StatMech.Walls
