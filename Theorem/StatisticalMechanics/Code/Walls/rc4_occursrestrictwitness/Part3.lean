/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Def.StatisticalMechanics.Code.Walls.rc4_occursrestrictwitness.Part3
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}


theorem pocUnrestrict_apply_differ (k : ConfigSpace α × ConfigSpace α)
    (σ : ConfigSpace (DifferSub k)) {a : α} (h : k.1 a ≠ k.2 a) :
    pocUnrestrict k σ a = σ ⟨a, h⟩ := by
  simp only [pocUnrestrict, dif_pos h]


theorem pocUnrestrict_apply_nondiffer (k : ConfigSpace α × ConfigSpace α)
    (σ : ConfigSpace (DifferSub k)) {a : α} (h : k.1 a = k.2 a) :
    pocUnrestrict k σ a = k.1 a := by
  simp only [pocUnrestrict, dif_neg (by simp [h] : ¬ k.1 a ≠ k.2 a)]


@[simp] theorem pocRestrict_pocUnrestrict (k : ConfigSpace α × ConfigSpace α)
    (σ : ConfigSpace (DifferSub k)) : pocRestrict k (pocUnrestrict k σ) = σ := by
  funext s
  simp only [pocRestrict_apply]
  exact pocUnrestrict_apply_differ k σ s.2


end StatMech.Walls
