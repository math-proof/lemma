/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Def.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem daep_mem_cutArmEnds {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x a z : Site d} :
    z ∈ daep_cutArmEnds ω n x a ↔ z ∈ vertexBoundary d n ∧ Connected d (removeSite x ω) a z := by
  classical
  rw [daep_cutArmEnds, Finset.mem_filter, tfc_mem_boundaryFinset]


theorem daep_cutArmEnds_subset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x a : Site d) :
    daep_cutArmEnds ω n x a ⊆ tfc_boundaryFinset d n := by
  classical
  exact Finset.filter_subset _ _


theorem daep_cutArmEnds_disjoint_of_disconnected (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a₁ a₂ : Site d} (hdis : ¬ Connected d (removeSite x ω) a₁ a₂) :
    Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₂) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_cutArmEnds] at hw1 hw2
  exact hdis (hw1.2.trans hw2.2.symm)


theorem daep_cutArmEnds_nonempty (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x a : Site d) (habox : a ∈ box d n) (hinf : (cluster d (removeSite x ω) a).Infinite) :
    (daep_cutArmEnds ω n x a).Nonempty := by
  classical
  obtain ⟨z, hzb, hzc⟩ := bk2_branch_reaches_boundary_rem ω n hn x a habox hinf
  exact ⟨z, daep_mem_cutArmEnds.mpr ⟨hzb, hzc⟩⟩


theorem daep_three_cut_blocks_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    {x a₁ a₂ a₃ : Site d}
    (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n) (ha3box : a₃ ∈ box d n)
    (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite x ω) a₃).Infinite)
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    ((daep_cutArmEnds ω n x a₁).Nonempty ∧ (daep_cutArmEnds ω n x a₂).Nonempty ∧
      (daep_cutArmEnds ω n x a₃).Nonempty) ∧
    (daep_cutArmEnds ω n x a₁ ⊆ tfc_boundaryFinset d n ∧
      daep_cutArmEnds ω n x a₂ ⊆ tfc_boundaryFinset d n ∧
      daep_cutArmEnds ω n x a₃ ⊆ tfc_boundaryFinset d n) ∧
    (Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₂) ∧
      Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₃) ∧
      Disjoint (daep_cutArmEnds ω n x a₂) (daep_cutArmEnds ω n x a₃)) :=
  ⟨⟨daep_cutArmEnds_nonempty ω n hn x a₁ ha1box hi1,
    daep_cutArmEnds_nonempty ω n hn x a₂ ha2box hi2,
    daep_cutArmEnds_nonempty ω n hn x a₃ ha3box hi3⟩,
   ⟨daep_cutArmEnds_subset ω n x a₁, daep_cutArmEnds_subset ω n x a₂,
    daep_cutArmEnds_subset ω n x a₃⟩,
   ⟨daep_cutArmEnds_disjoint_of_disconnected ω n hd12,
    daep_cutArmEnds_disjoint_of_disconnected ω n hd13,
    daep_cutArmEnds_disjoint_of_disconnected ω n hd23⟩⟩


theorem daep_doubleCut_le (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    removeSite x (removeSite y ω) ≤ ω := by
  intro e
  unfold removeSite
  by_cases hx : x ∈ e
  · simp [hx]
  · by_cases hy : y ∈ e <;> simp [hx, hy]


theorem daep_doubleCut_arms_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y a b : Site d}
    (hdis : ¬ Connected d (removeSite x (removeSite y ω)) a b) :
    Disjoint (daep_cutArmEnds (removeSite y ω) n x a)
      (daep_cutArmEnds (removeSite x ω) n y b) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_cutArmEnds] at hw1 hw2
  
  have hsymm : removeSite y (removeSite x ω) = removeSite x (removeSite y ω) := by
    funext e
    unfold removeSite
    by_cases hx : x ∈ e <;> by_cases hy : y ∈ e <;> simp [hx, hy]
  have hwa : Connected d (removeSite x (removeSite y ω)) a w := hw1.2
  have hwb : Connected d (removeSite x (removeSite y ω)) b w := by
    rw [← hsymm]; exact hw2.2
  exact hdis (hwa.trans hwb.symm)


end Percolation
end StatMech
