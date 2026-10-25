/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc4_adj_origin_sum (n : Site d) (h : (hypercubicLattice d).Adj 0 n) :
    ∑ j, (n j).natAbs = 1 := by
  rw [hypercubicLattice_adj] at h
  simpa [Int.natAbs_neg] using h


theorem bc4_witness_coord (n : Site d) (h : ∑ j, (n j).natAbs = 1) :
    ∃ i, (n i = 1 ∨ n i = -1) ∧ ∀ j, j ≠ i → n j = 0 := by
  
  obtain ⟨i, _, hzero⟩ : ∃ i ∈ Finset.univ, (n i).natAbs ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not, Finset.mem_univ,
      forall_true_left] at hcon
    have : ∑ j, (n j).natAbs = 0 := Finset.sum_eq_zero (fun j _ => hcon j)
    omega
  
  have hni1 : (n i).natAbs = 1 := by
    have hle : (n i).natAbs ≤ ∑ j, (n j).natAbs :=
      Finset.single_le_sum (f := fun j => (n j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hle; omega
  refine ⟨i, ?_, ?_⟩
  · rcases Int.natAbs_eq_iff.mp hni1 with h1 | h1
    · left; simpa using h1
    · right; simpa using h1
  · 
    intro j hj
    by_contra hnj
    have hjpos : (n j).natAbs ≥ 1 := by
      have := Int.natAbs_eq_zero.not.mpr hnj; omega
    have hsub : ({i, j} : Finset (Fin d)) ⊆ Finset.univ := fun k _ => Finset.mem_univ k
    have hpair : ∑ k ∈ ({i, j} : Finset (Fin d)), (n k).natAbs
        = (n i).natAbs + (n j).natAbs := Finset.sum_pair (Ne.symm hj)
    have hbig : ∑ k ∈ ({i, j} : Finset (Fin d)), (n k).natAbs ≤ ∑ k, (n k).natAbs :=
      Finset.sum_le_sum_of_subset hsub
    rw [hpair, h] at hbig; omega


theorem bc4_openNbr_adj (ω : ConfigSpace (Sym2 (Site d))) {n : Site d}
    (hn : (openSubgraph d ω).Adj 0 n) : (hypercubicLattice d).Adj 0 n := hn.1


theorem bc4_openNbr_mem_box_one (ω : ConfigSpace (Sym2 (Site d))) {n : Site d}
    (hn : (openSubgraph d ω).Adj 0 n) : n ∈ box d 1 := by
  rw [mem_box]
  intro i
  have hadj : (hypercubicLattice d).Adj 0 n := bc4_openNbr_adj ω hn
  rw [hypercubicLattice_adj] at hadj
  
  have hle : ((0 : Site d) i - n i).natAbs ≤ ∑ j, ((0 : Site d) j - n j).natAbs :=
    Finset.single_le_sum (f := fun j => ((0 : Site d) j - n j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hadj] at hle
  simpa using hle


theorem bc4_origin_openNeighbours_subset_box (ω : ConfigSpace (Sym2 (Site d))) :
    {n : Site d | (openSubgraph d ω).Adj 0 n} ⊆ box d 1 :=
  fun _ hn => bc4_openNbr_mem_box_one ω hn


theorem bc4_origin_openNeighbours_finite (ω : ConfigSpace (Sym2 (Site d))) :
    {n : Site d | (openSubgraph d ω).Adj 0 n}.Finite :=
  (box_finite d 1).subset (bc4_origin_openNeighbours_subset_box ω)


end Walls
end StatMech
