/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc89bmetricinjection.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc90b_ncount_mono (ends : ι → Sym2 W) {R R' : Finset ι} (hRR : R ⊆ R') :
    gc86b_ncount ends R ∅ ≤ gc86b_ncount ends R' ∅ := by
  unfold gc86b_ncount
  apply Finset.card_le_card
  intro K hK
  simp only [Finset.mem_filter, Finset.mem_powerset] at hK ⊢
  exact ⟨hK.1.trans hRR, hK.2⟩


theorem gc90b_perK1_le (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hP : P ⊆ K₁) :
    gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ (K₁ \ P)) ∅ := by
  apply gc90b_ncount_mono
  apply Finset.sdiff_subset_sdiff (Finset.Subset.refl m)
  exact Finset.sdiff_subset


end StatMech.Walls
