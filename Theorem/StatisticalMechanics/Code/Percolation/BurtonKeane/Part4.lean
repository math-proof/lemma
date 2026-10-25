/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.Percolation.BurtonKeane.Part2
open MeasureTheory

set_option linter.style.show false


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


lemma smul_injective (g : Multiplicative (Site d)) :
    Function.Injective (fun y : Site d => g • y) := fun _ _ h => by simpa using h


lemma image_smul_injective (g : Multiplicative (Site d)) :
    Function.Injective (fun C : Set (Site d) => (fun y => g • y) '' C) := fun _ _ h =>
  (Set.image_injective.mpr (smul_injective g)) h


lemma infiniteClusters_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) :
    infiniteClusters d (shift g ω)
      = (fun C => (fun y => g • y) '' C) '' (infiniteClusters d ω) := by
  ext C
  simp only [infiniteClusters, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hinf, x, rfl⟩
    refine ⟨cluster d ω (g⁻¹ • x), ⟨?_, g⁻¹ • x, rfl⟩, ?_⟩
    · have hc := cluster_shift g ω (g⁻¹ • x)
      rw [smul_inv_smul] at hc
      rw [hc] at hinf
      exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf
    · have hc := cluster_shift g ω (g⁻¹ • x)
      rw [smul_inv_smul] at hc
      exact hc.symm
  · rintro ⟨C, ⟨hinf, x, rfl⟩, rfl⟩
    refine ⟨?_, g • x, ?_⟩
    · exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf
    · exact (cluster_shift g ω x).symm


theorem numInfiniteClusters_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) :
    numInfiniteClusters d (shift g ω) = numInfiniteClusters d ω := by
  unfold numInfiniteClusters
  rw [infiniteClusters_shift]
  exact Set.InjOn.encard_image (Set.injOn_of_injective (image_smul_injective g))


lemma measurableSet_openAdj (x y : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x y} := by
  by_cases h : (hypercubicLattice d).Adj x y
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x y}
        = {ω | ω s(x, y) = true} := by
      ext ω
      rw [Set.mem_setOf_eq, openSubgraph_adj]
      simp only [Set.mem_setOf_eq]
      exact ⟨fun hh => hh.2, fun hh => ⟨h, hh⟩⟩
    rw [heq]
    exact measurableSet_eq_fun (StatMech.ConfigSpace.measurable_eval s(x, y)) measurable_const
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x y} = ∅ := by
      ext ω
      rw [Set.mem_setOf_eq, openSubgraph_adj]
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hh => h hh.1
    rw [heq]; exact MeasurableSet.empty


lemma measurableSet_isChain (l : List (Site d)) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj l} := by
  induction l with
  | nil =>
      have heq : {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj []}
          = Set.univ := by ext ω; simp [List.IsChain.nil]
      rw [heq]; exact MeasurableSet.univ
  | cons a l ih =>
      cases l with
      | nil =>
          have heq : {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj [a]}
              = Set.univ := by ext ω; simp [List.IsChain.singleton]
          rw [heq]; exact MeasurableSet.univ
      | cons b l' =>
          have heq :
              {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj (a :: b :: l')}
                = {ω | (openSubgraph d ω).Adj a b}
                    ∩ {ω | List.IsChain (openSubgraph d ω).Adj (b :: l')} := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.isChain_cons_cons]
          rw [heq]
          exact (measurableSet_openAdj a b).inter ih


lemma connected_iff_chain (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    Connected d ω x y ↔
      ∃ l : List (Site d), ∃ h : (x :: l) ≠ [],
        List.IsChain (openSubgraph d ω).Adj (x :: l) ∧ (x :: l).getLast h = y := by
  unfold Connected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    obtain ⟨l, hchain, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    exact ⟨l, List.cons_ne_nil _ _, hchain, hlast⟩
  · rintro ⟨l, _, hchain, hlast⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hchain hlast


lemma measurableSet_connected (x y : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω x y} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω x y}
      = ⋃ l : List (Site d), ({ω | List.IsChain (openSubgraph d ω).Adj (x :: l)}
            ∩ (if (x :: l).getLast (List.cons_ne_nil _ _) = y then Set.univ else ∅)) := by
    ext ω
    rw [Set.mem_setOf_eq, connected_iff_chain]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨l, _, hchain, hlast⟩
      exact ⟨l, hchain, by rw [if_pos (by simpa using hlast)]; trivial⟩
    · rintro ⟨l, hchain, hlast⟩
      refine ⟨l, List.cons_ne_nil _ _, hchain, ?_⟩
      by_cases hh : (x :: l).getLast (List.cons_ne_nil _ _) = y
      · exact hh
      · rw [if_neg hh] at hlast; exact absurd hlast (Set.notMem_empty _)
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  apply MeasurableSet.inter (measurableSet_isChain (x :: l))
  by_cases hh : (x :: l).getLast (List.cons_ne_nil _ _) = y
  · rw [if_pos hh]; exact MeasurableSet.univ
  · rw [if_neg hh]; exact MeasurableSet.empty


lemma finite_subset_box (S : Set (Site d)) (hS : S.Finite) : ∃ n, S ⊆ box d n := by
  classical
  refine ⟨hS.toFinset.sup (fun x => Finset.univ.sup (fun i => (x i).natAbs)), ?_⟩
  intro x hx i
  have hxmem : x ∈ hS.toFinset := by rwa [Set.Finite.mem_toFinset]
  calc (x i).natAbs ≤ Finset.univ.sup (fun i => (x i).natAbs) :=
          Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
    _ ≤ hS.toFinset.sup (fun x => Finset.univ.sup (fun i => (x i).natAbs)) :=
          Finset.le_sup (f := fun x => Finset.univ.sup (fun i => (x i).natAbs)) hxmem


lemma cluster_infinite_iff (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    (cluster d ω x).Infinite ↔ ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d ω x y := by
  constructor
  · intro hinf n
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hsub : cluster d ω x ⊆ box d n := fun y hy => by
      by_contra hyb; exact (hcon y hyb) hy
    exact hinf ((box_finite d n).subset hsub)
  · intro h hfin
    obtain ⟨n, hn⟩ := finite_subset_box _ hfin
    obtain ⟨y, hyb, hyc⟩ := h n
    exact hyb (hn hyc)


lemma measurableSet_clusterInfinite (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d ω x).Infinite} := by
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d ω x).Infinite}
      = ⋂ n : ℕ, ⋃ y ∈ {y : Site d | y ∉ box d n}, {ω | Connected d ω x y} := by
    ext ω
    rw [Set.mem_setOf_eq, cluster_infinite_iff]
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h n
      obtain ⟨y, hyb, hyc⟩ := h n
      exact ⟨y, hyb, hyc⟩
    · intro h n
      obtain ⟨y, hyb, hyc⟩ := h n
      exact ⟨y, hyb, hyc⟩
  rw [heq]
  apply MeasurableSet.iInter; intro n
  apply MeasurableSet.biUnion (Set.to_countable _); intro y _
  exact measurableSet_connected x y


lemma exists_encode_min (S : Set (Site d)) (hne : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, Encodable.encode x ≤ Encodable.encode y := by
  obtain ⟨x₀, hx₀⟩ := hne
  classical
  have hmT : sInf (Encodable.encode '' S) ∈ Encodable.encode '' S :=
    Nat.sInf_mem ⟨Encodable.encode x₀, x₀, hx₀, rfl⟩
  obtain ⟨x, hxS, hxm⟩ := hmT
  exact ⟨x, hxS, fun y hy => hxm ▸ Nat.sInf_le ⟨y, hy, rfl⟩⟩


end Percolation
end StatMech
