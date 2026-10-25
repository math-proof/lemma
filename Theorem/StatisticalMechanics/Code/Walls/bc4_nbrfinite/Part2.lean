/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.Walls.bc4_nbrfinite
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc4_nbrKey_eq [NeZero d] (n : Site d) (h : ∑ j, (n j).natAbs = 1) :
    bc4_nbrKey n
      = ((bc4_witness_coord n h).choose,
         decide (n ((bc4_witness_coord n h).choose) = 1)) := by
  simp only [bc4_nbrKey]; rw [dif_pos h]


theorem bc4_nbrKey_witness [NeZero d] (n : Site d) (h : ∑ j, (n j).natAbs = 1) :
    (n (bc4_nbrKey n).1 = 1 ∨ n (bc4_nbrKey n).1 = -1)
      ∧ (∀ j, j ≠ (bc4_nbrKey n).1 → n j = 0)
      ∧ (bc4_nbrKey n).2 = decide (n (bc4_nbrKey n).1 = 1) := by
  rw [bc4_nbrKey_eq n h]
  exact ⟨(bc4_witness_coord n h).choose_spec.1,
    (bc4_witness_coord n h).choose_spec.2, rfl⟩


theorem bc4_nbr_eq_of_key {n m : Site d} {i : Fin d}
    (hn1 : n i = 1 ∨ n i = -1) (hnz : ∀ j, j ≠ i → n j = 0)
    (hm1 : m i = 1 ∨ m i = -1) (hmz : ∀ j, j ≠ i → m j = 0)
    (hsign : decide (n i = 1) = decide (m i = 1)) : n = m := by
  
  have hsig : (n i = 1) ↔ (m i = 1) := by
    constructor <;> intro h <;> simp_all
  funext j
  by_cases hj : j = i
  · subst hj
    rcases hn1 with h | h <;> rcases hm1 with h' | h' <;> simp_all
  · rw [hnz j hj, hmz j hj]


theorem bc4_nbrKey_injOn [NeZero d] :
    Set.InjOn bc4_nbrKey {n : Site d | (hypercubicLattice d).Adj 0 n} := by
  intro n hn m hm hkey
  have hns : ∑ j, (n j).natAbs = 1 := bc4_adj_origin_sum n hn
  have hms : ∑ j, (m j).natAbs = 1 := bc4_adj_origin_sum m hm
  obtain ⟨hn1, hnz, hnsgn⟩ := bc4_nbrKey_witness n hns
  obtain ⟨hm1, hmz, hmsgn⟩ := bc4_nbrKey_witness m hms
  
  have hi : (bc4_nbrKey n).1 = (bc4_nbrKey m).1 := by rw [hkey]
  
  rw [hi] at hn1 hnz hnsgn
  set j := (bc4_nbrKey m).1 with hjdef
  have hsgn : decide (n j = 1) = decide (m j = 1) := by
    rw [← hnsgn, ← hmsgn, hkey]
  exact bc4_nbr_eq_of_key hn1 hnz hm1 hmz hsgn


theorem bc4_origin_latticeNeighbours_ncard_le_pos [NeZero d] :
    {n : Site d | (hypercubicLattice d).Adj 0 n}.ncard ≤ 2 * d := by
  classical
  have hinj := bc4_nbrKey_injOn (d := d)
  
  rw [← hinj.ncard_image]
  have hsub : bc4_nbrKey '' {n : Site d | (hypercubicLattice d).Adj 0 n}
      ⊆ (Set.univ : Set (Fin d × Bool)) := Set.subset_univ _
  calc (bc4_nbrKey '' {n : Site d | (hypercubicLattice d).Adj 0 n}).ncard
      ≤ (Set.univ : Set (Fin d × Bool)).ncard :=
        Set.ncard_le_ncard hsub Set.finite_univ
    _ = Fintype.card (Fin d × Bool) := by
        rw [Set.ncard_univ]; simp [Nat.card_eq_fintype_card]
    _ = 2 * d := by simp [Fintype.card_prod, mul_comm]


theorem bc4_origin_latticeNeighbours_ncard_le :
    {n : Site d | (hypercubicLattice d).Adj 0 n}.ncard ≤ 2 * d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    
    have : {n : Site 0 | (hypercubicLattice 0).Adj 0 n} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hadj
      have := bc4_adj_origin_sum n hadj
      simp at this
    rw [this]; simp
  · haveI : NeZero d := ⟨hd.ne'⟩
    exact bc4_origin_latticeNeighbours_ncard_le_pos


theorem bc4_origin_openNeighbours_ncard_le (ω : ConfigSpace (Sym2 (Site d))) :
    {n : Site d | (openSubgraph d ω).Adj 0 n}.ncard ≤ 2 * d := by
  refine le_trans (Set.ncard_le_ncard ?_ ?_) bc4_origin_latticeNeighbours_ncard_le
  · intro n hn; exact bc4_openNbr_adj ω hn
  · 
    apply (box_finite d 1).subset
    intro n hn
    rw [mem_box]
    intro i
    have hadj : (hypercubicLattice d).Adj 0 n := hn
    rw [hypercubicLattice_adj] at hadj
    have hle : ((0 : Site d) i - n i).natAbs ≤ ∑ j, ((0 : Site d) j - n j).natAbs :=
      Finset.single_le_sum (f := fun j => ((0 : Site d) j - n j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hadj] at hle
    simpa using hle

end Walls
end StatMech
