/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCutParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSourceToggle
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

namespace ReplicaCutParity

open StatMech.Sharpness.RandomCurrent

variable {W ι : Type*} [Fintype W] [DecidableEq W]
  [Fintype ι] [DecidableEq ι]

theorem edge_side_card_even_of_no_cross
    (ends : ι -> Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
    (S : Finset W)
    (hno : ∀ {u v}, u ∈ S -> v ∉ S ->
      ¬ RandomCurrent.connK ends K u v)
    {i : ι} (hi : i ∈ K) :
    Even (#(S.filter fun x => x ∈ ends i)) := by
  obtain ⟨⟨a, b⟩, hab⟩ := (ends i).exists_rep
  have hne : a ≠ b := by
    intro h
    subst b
    exact hnd i hi (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
  have hset :
      S.filter (fun x => x ∈ ends i) =
        ({a, b} : Finset W).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_filter, ← hab, Sym2.mem_iff,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hsides : a ∈ S ↔ b ∈ S := by
    constructor
    · intro ha
      by_contra hb
      exact hno ha hb (Relation.ReflTransGen.single
        ⟨i, hi, hab ▸ Sym2.mem_mk_left a b,
          hab ▸ Sym2.mem_mk_right a b, hne⟩)
    · intro hb
      by_contra ha
      exact hno hb ha (Relation.ReflTransGen.single
        ⟨i, hi, hab ▸ Sym2.mem_mk_right a b,
          hab ▸ Sym2.mem_mk_left a b, hne.symm⟩)
  rw [hset]
  by_cases ha : a ∈ S
  · have hb := hsides.mp ha
    rw [Finset.filter_insert, Finset.filter_singleton,
      if_pos ha, if_pos hb,
      Finset.card_insert_of_notMem (by simp [hne]),
      Finset.card_singleton]
    exact ⟨1, rfl⟩
  · have hb : b ∉ S := fun h => ha (hsides.mpr h)
    rw [Finset.filter_insert, Finset.filter_singleton,
      if_neg ha, if_neg hb]
    simp


theorem sources_inter_even_of_no_cross
    (ends : ι -> Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
    (S : Finset W)
    (hno : ∀ {u v}, u ∈ S -> v ∉ S ->
      ¬ RandomCurrent.connK ends K u v) :
    Even (#(RandomCurrent.sources ends K ∩ S)) := by
  have hsumEq :
      (∑ x ∈ S, RandomCurrent.degK ends K x) =
        ∑ i ∈ K, #(S.filter fun x => x ∈ ends i) := by
    unfold RandomCurrent.degK
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hsum : Even (∑ x ∈ S, RandomCurrent.degK ends K x) := by
    rw [hsumEq]
    exact Finset.even_sum _ fun i hi =>
      edge_side_card_even_of_no_cross ends K hnd S hno hi
  have hcount := (RandomCurrent.even_sum_iff_even_count S
    (RandomCurrent.degK ends K)).mp hsum
  convert hcount using 1
  congr 1
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter,
    RandomCurrent.mem_sources]
  tauto


theorem exists_cross_connection_of_odd_sources
    (ends : ι -> Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
    (S : Finset W)
    (hodd : Odd (#(RandomCurrent.sources ends K ∩ S))) :
    ∃ u ∈ S, ∃ v ∉ S, RandomCurrent.connK ends K u v := by
  by_contra h
  push_neg at h
  have heven := sources_inter_even_of_no_cross ends K hnd S
    (fun {_ _} hu hv => h _ hu _ hv)
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end ReplicaCutParity
end
end StatMech.Ising
