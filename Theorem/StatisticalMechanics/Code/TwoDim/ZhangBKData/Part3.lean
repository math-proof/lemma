/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


theorem zbd_connectedWithinBox_subset_connected {d : ℕ} (x y : Site d) (n : ℕ) :
    zbd_connectedWithinBox x y n ⊆ {omega | Connected d omega x y} := by
  rintro omega ⟨_hx, _hy, hxy⟩
  exact hxy.connected


theorem zbd_iUnion_connectedWithinBox {d : ℕ} (x y : Site d) :
    (⋃ n, zbd_connectedWithinBox x y n) = {omega | Connected d omega x y} := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun n => zbd_connectedWithinBox_subset_connected x y n
  · intro omega hxy
    obtain ⟨n, hx, hy, hwithin⟩ := zbd_connectedWithin_box_of_connected omega hxy
    exact Set.mem_iUnion.mpr ⟨n, hx, hy, hwithin⟩


theorem zbd_measurableSet_connectedWithin {d : ℕ} (S : Set (Site d)) (x y : S) :
    MeasurableSet {omega : ConfigSpace (Sym2 (Site d)) |
      ConnectedWithin d omega S x y} := by
  classical
  have hchain : ∀ l : List S,
      MeasurableSet {omega : ConfigSpace (Sym2 (Site d)) |
        List.IsChain (openSubgraphInduce d omega S).Adj l} := by
    intro l
    induction l with
    | nil => simpa using (MeasurableSet.univ : MeasurableSet
        (Set.univ : Set (ConfigSpace (Sym2 (Site d)))))
    | cons a l ih =>
        cases l with
        | nil => simpa using (MeasurableSet.univ : MeasurableSet
            (Set.univ : Set (ConfigSpace (Sym2 (Site d)))))
        | cons b l' =>
            have heq :
                {omega : ConfigSpace (Sym2 (Site d)) |
                    List.IsChain (openSubgraphInduce d omega S).Adj (a :: b :: l')}
                  = {omega | (openSubgraph d omega).Adj (a : Site d) (b : Site d)} ∩
                    {omega | List.IsChain (openSubgraphInduce d omega S).Adj (b :: l')} := by
              ext omega
              simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.isChain_cons_cons,
                openSubgraphInduce_adj]
            rw [heq]
            exact (measurableSet_openAdj (a : Site d) (b : Site d)).inter ih
  have heq :
      {omega : ConfigSpace (Sym2 (Site d)) | ConnectedWithin d omega S x y} =
        ⋃ l : List S,
          ({omega | List.IsChain (openSubgraphInduce d omega S).Adj (x :: l)} ∩
            if (x :: l).getLast (List.cons_ne_nil _ _) = y then Set.univ else ∅) := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    unfold ConnectedWithin
    rw [SimpleGraph.reachable_iff_reflTransGen]
    constructor
    · intro h
      obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
      exact ⟨l, hl, by simp [hlast]⟩
    · rintro ⟨l, hl, hlast⟩
      have heqLast : (x :: l).getLast (List.cons_ne_nil _ _) = y := by
        by_contra hne
        simp [hne] at hlast
      exact List.relationReflTransGen_of_exists_isChain_cons l hl heqLast
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  apply (hchain (x :: l)).inter
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

theorem zbd_connectedWithinBox_measurableSet {d : ℕ} (x y : Site d) (n : ℕ) :
    MeasurableSet (zbd_connectedWithinBox x y n) := by
  classical
  by_cases hx : x ∈ box d n
  · by_cases hy : y ∈ box d n
    · have heq : zbd_connectedWithinBox x y n =
          {omega | ConnectedWithin d omega (box d n) ⟨x, hx⟩ ⟨y, hy⟩} := by
        ext omega
        simp only [zbd_connectedWithinBox, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hx', hy', h⟩
          simpa using h
        · intro h
          exact ⟨hx, hy, h⟩
      rw [heq]
      exact zbd_measurableSet_connectedWithin (box d n) ⟨x, hx⟩ ⟨y, hy⟩
    · have : zbd_connectedWithinBox x y n = ∅ := by
        ext omega
        simp [zbd_connectedWithinBox, hy]
      rw [this]
      exact MeasurableSet.empty
  · have : zbd_connectedWithinBox x y n = ∅ := by
      ext omega
      simp [zbd_connectedWithinBox, hx]
    rw [this]
    exact MeasurableSet.empty


end StatMech.TwoDim
