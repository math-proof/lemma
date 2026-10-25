/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jgc_pend_core_adj (i j : Fin 5) : jgc_pend_core.Adj i j ↔
    ((i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) ||
     (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3) : Bool) :=
  Iff.rfl


theorem jgc_pend_leaf_uniq : ∀ w, jgc_pend_G.Adj 4 w → w = 0 := by
  intro w h; rw [jgc_pend_G_adj] at h; revert h; fin_cases w <;> simp [jgc_pend_rel]

theorem jgc_pend_leaf_adj : jgc_pend_G.Adj 4 0 := by rw [jgc_pend_G_adj]; decide


theorem jgc_pend_delete_eq_core :
    jgc_pend_G.deleteEdges {s((4 : Fin 5), 0)} = jgc_pend_core := by
  ext i j
  rw [deleteEdges_adj, jgc_pend_G_adj, jgc_pend_core_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  revert i j; decide


theorem jgc_pend_core_isCycles : jgc_pend_core.IsCycles := by
  intro v hv
  rw [Set.ncard_eq_two]
  fin_cases v
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet] <;> decide⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet] <;> decide⟩
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet] <;> decide⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet] <;> decide⟩
  · 
    exfalso
    obtain ⟨w, hw⟩ := hv
    rw [SimpleGraph.mem_neighborSet, jgc_pend_core_adj] at hw
    revert hw; fin_cases w <;> decide


theorem jgc_pend_isCactus : jgc_IsCactus jgc_pend_G := by
  refine jgc_IsCactus.leaf jgc_pend_leaf_adj jgc_pend_leaf_uniq ?_
  rw [jgc_pend_delete_eq_core]
  exact jgc_isCactus_of_isCycles jgc_pend_core jgc_pend_core_isCycles


theorem jgc_pend_not_isCycles : ¬ jgc_pend_G.IsCycles := by
  intro hcyc
  have hv : (jgc_pend_G.neighborSet 0).Nonempty :=
    ⟨1, by rw [SimpleGraph.mem_neighborSet, jgc_pend_G_adj]; decide⟩
  have h2 := hcyc hv
  
  have h3 : jgc_pend_G.neighborSet 0 = {1, 3, 4} := by
    ext w; rw [SimpleGraph.mem_neighborSet, jgc_pend_G_adj]
    fin_cases w <;> simp [jgc_pend_rel]
  rw [h3] at h2
  rw [show ({1, 3, 4} : Set (Fin 5)).ncard = 3 by
    rw [Set.ncard_eq_toFinset_card']; decide] at h2
  exact absurd h2 (by decide)


theorem jgc_faithfulDiscreteJordan_pendantSquare : whc_FaithfulDiscreteJordan jgc_pend_P :=
  jgc_faithfulDiscreteJordan jgc_pend_P jgc_pend_isCactus


end Lattice
end StatMech
