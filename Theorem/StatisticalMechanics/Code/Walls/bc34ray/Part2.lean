/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc33escaping.Part2
import Def.StatisticalMechanics.Code.Walls.bc34ray.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem ray34_kstep_adj {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]
    (s : ray34_KState G) : G.Adj s.1.2 (ray34_kstep G s).1.2 :=
  (ray34_konig_step s.2.1 s.2.2).choose_spec.1


theorem ray34_kstep_fst {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]
    (s : ray34_KState G) : (ray34_kstep G s).1.1 = insert s.1.2 s.1.1 := rfl


theorem ray34_konig {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]
    {S : Set V} {v : V} (hv : v ∉ S) (hinf : (ray34_AvoidCluster G S v).Infinite) :
    ∃ r : ℕ → V, r 0 = v ∧ Function.Injective r ∧
      (∀ k, G.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ S) := by
  classical
  
  set s0 : ray34_KState G := ⟨(S, v), hv, hinf⟩ with hs0
  set state : ℕ → ray34_KState G := fun n => Nat.rec s0 (fun _ s => ray34_kstep G s) n with hstate
  set r : ℕ → V := fun n => (state n).1.2 with hr
  have hstate_succ : ∀ n, state (n + 1) = ray34_kstep G (state n) := fun n => rfl
  
  have hmono : ∀ n, (state n).1.1 ⊆ (state (n + 1)).1.1 := by
    intro n
    rw [hstate_succ, ray34_kstep_fst]
    exact Set.subset_insert _ _
  have hmono_le : ∀ {m n}, m ≤ n → (state m).1.1 ⊆ (state n).1.1 := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  have hScontained : ∀ n, S ⊆ (state n).1.1 := by
    intro n
    have h0 : (state 0).1.1 = S := rfl
    have := hmono_le (Nat.zero_le n)
    rwa [h0] at this
  
  have hnotin : ∀ n, r n ∉ (state n).1.1 := fun n => (state n).2.1
  
  have hravoid : ∀ n, r n ∉ S := fun n hn => hnotin n (hScontained n hn)
  
  have hr_in_later : ∀ {m n}, m < n → r m ∈ (state n).1.1 := by
    intro m n hmn
    have hm1 : m + 1 ≤ n := hmn
    have : r m ∈ (state (m + 1)).1.1 := by
      rw [hstate_succ, ray34_kstep_fst]; exact Set.mem_insert _ _
    exact hmono_le hm1 this
  
  have hinj : Function.Injective r := by
    intro a b hab
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · 
      exact hnotin b (hab ▸ hr_in_later h)
    · rcases lt_of_le_of_ne h (Ne.symm hne) with h'
      exact hnotin a (hab.symm ▸ hr_in_later h')
  refine ⟨r, rfl, hinj, ?_, hravoid⟩
  intro k
  have := ray34_kstep_adj G (state k)
  rwa [← hstate_succ k] at this


open Classical in


theorem ray34_avoidCluster_diff_subset_biUnion_gen {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [LocallyFinite G] {S : Set V} (v t : V) :
    ray34_AvoidCluster G S v \ {t} ⊆
      ray34_AvoidCluster G (insert t S) v ∪
      ⋃ w ∈ (G.neighborFinset t).filter (· ∉ insert t S),
        ray34_AvoidCluster G (insert t S) w := by
  intro z hz
  obtain ⟨hzc, hzt⟩ := hz
  simp only [Set.mem_singleton_iff] at hzt
  obtain ⟨p, hp⟩ := hzc
  set q := p.toPath with hq
  have hqsub : (q : G.Walk v z).support ⊆ p.support := p.support_toPath_subset
  have hqpath : (q : G.Walk v z).IsPath := q.2
  have hqavoid : ∀ u ∈ (q : G.Walk v z).support, u ∉ S := fun u hu => hp u (hqsub hu)
  by_cases htq : t ∈ (q : G.Walk v z).support
  · 
    right
    set qd := (q : G.Walk v z).dropUntil t htq with hqd
    have hqdsub : qd.support ⊆ (q : G.Walk v z).support := (q : G.Walk v z).support_dropUntil_subset htq
    
    have hqdavoid : ∀ u ∈ qd.support, u ∉ S := fun u hu => hqavoid u (hqdsub hu)
    have hqdpath : qd.IsPath := hqpath.dropUntil htq
    
    obtain ⟨w, hadj, q', hcons⟩ := Walk.exists_eq_cons_of_ne (Ne.symm hzt) qd
    have hqdcons : qd = Walk.cons hadj q' := hcons
    have hqdpath' : (Walk.cons hadj q').IsPath := hqdcons ▸ hqdpath
    have hvnotin : t ∉ q'.support := ((Walk.cons_isPath_iff hadj q').mp hqdpath').2
    have hwS : w ∉ S := by
      apply hqdavoid w
      rw [hqdcons, Walk.support_cons]
      exact List.mem_cons.mpr (Or.inr q'.start_mem_support)
    have hq'avoid : ∀ u ∈ q'.support, u ∉ insert t S := by
      intro u hu
      rw [Set.mem_insert_iff]; push Not
      refine ⟨?_, ?_⟩
      · rintro rfl; exact hvnotin hu
      · apply hqdavoid u
        rw [hqdcons, Walk.support_cons]
        exact List.mem_cons.mpr (Or.inr hu)
    rw [Set.mem_iUnion₂]
    refine ⟨w, ?_, ⟨q', hq'avoid⟩⟩
    rw [Finset.mem_filter, mem_neighborFinset, Set.mem_insert_iff]
    push Not
    exact ⟨hadj, fun heq => (hadj.ne heq.symm).elim, hwS⟩
  · 
    left
    refine ⟨(q : G.Walk v z), ?_⟩
    intro u hu
    rw [Set.mem_insert_iff]; push Not
    refine ⟨?_, hqavoid u hu⟩
    rintro rfl; exact htq hu


theorem ray34_root_mem_of_piece_meets {V : Type*} {G : SimpleGraph V} {S : Set V} {t v w z : V}
    (hz1 : z ∈ ray34_AvoidCluster G (insert t S) w) (hz2 : z ∈ ray34_AvoidCluster G S v) :
    w ∈ ray34_AvoidCluster G S v := by
  have hwz : ray34_AvoidReach G S w z :=
    ray34_avoidCluster_mono (Set.subset_insert t S) w hz1
  exact ray34_avoidReach_trans hz2 (ray34_avoidReach_symm hwz)


theorem ray34_avoidCluster_step {V : Type*} [DecidableEq V] {G : SimpleGraph V} [LocallyFinite G]
    {S : Set V} {v : V} (hinf : (ray34_AvoidCluster G S v).Infinite) (t : V) :
    ∃ b, b ∈ ray34_AvoidCluster G S v ∧ (ray34_AvoidCluster G (insert t S) b).Infinite := by
  classical
  
  have hvS : v ∉ S := ray34_notMem_of_avoidCluster_nonempty hinf.nonempty
  have hvc : v ∈ ray34_AvoidCluster G S v := ray34_self_mem_avoidCluster G S hvS
  have hdiff : (ray34_AvoidCluster G S v \ {t}).Infinite := hinf.diff (Set.finite_singleton t)
  have hcover := ray34_avoidCluster_diff_subset_biUnion_gen (G := G) (S := S) v t
  by_contra hcon
  push Not at hcon
  
  set C := ray34_AvoidCluster G S v with hC
  
  have hvfin : (ray34_AvoidCluster G (insert t S) v ∩ C).Finite :=
    (hcon v hvc).inter_of_left C
  
  have hfin : ∀ w ∈ (((G.neighborFinset t).filter (· ∉ insert t S) : Finset V) : Set V),
      (ray34_AvoidCluster G (insert t S) w ∩ C).Finite := by
    intro w _
    rcases (ray34_AvoidCluster G (insert t S) w ∩ C).eq_empty_or_nonempty with he | hne
    · rw [he]; exact Set.finite_empty
    · obtain ⟨z, hz1, hz2⟩ := hne
      have hwc : w ∈ C := ray34_root_mem_of_piece_meets hz1 hz2
      exact (hcon w hwc).inter_of_left C
  
  have hsub : ray34_AvoidCluster G S v \ {t} ⊆
      (ray34_AvoidCluster G (insert t S) v ∩ C) ∪
      ⋃ w ∈ (((G.neighborFinset t).filter (· ∉ insert t S) : Finset V) : Set V),
        (ray34_AvoidCluster G (insert t S) w ∩ C) := by
    intro z hz
    have hzC : z ∈ C := hz.1
    have := hcover hz
    rw [Set.mem_union, Set.mem_iUnion₂] at this ⊢
    rcases this with h | ⟨w, hw, hwz⟩
    · exact Or.inl ⟨h, hzC⟩
    · exact Or.inr ⟨w, hw, hwz, hzC⟩
  have hunionfin :
      ((ray34_AvoidCluster G (insert t S) v ∩ C) ∪
        ⋃ w ∈ (((G.neighborFinset t).filter (· ∉ insert t S) : Finset V) : Set V),
          (ray34_AvoidCluster G (insert t S) w ∩ C)).Finite :=
    hvfin.union (Set.Finite.biUnion (Finset.finite_toSet _) hfin)
  exact hdiff (hunionfin.subset hsub)


theorem ray34_infinite_avoidCluster_of_finset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [LocallyFinite G] {v : V} (hinf : (ray34_AvoidCluster G ∅ v).Infinite) (T : Finset V) :
    ∃ b, b ∈ ray34_AvoidCluster G ∅ v ∧ (ray34_AvoidCluster G (↑T) b).Infinite := by
  classical
  induction T using Finset.induction with
  | empty => exact ⟨v, ray34_self_mem_avoidCluster G ∅ (by simp), by simpa using hinf⟩
  | @insert t T' htT' ih =>
    obtain ⟨b, hb1, hb2⟩ := ih
    obtain ⟨b', hb'1, hb'2⟩ := ray34_avoidCluster_step hb2 t
    refine ⟨b', ?_, ?_⟩
    · 
      have hbb' : ray34_AvoidReach G ∅ b b' :=
        ray34_avoidCluster_mono (Set.empty_subset (↑T')) b hb'1
      exact ray34_avoidReach_trans hb1 hbb'
    · 
      rw [Finset.coe_insert]; exact hb'2


end StatMech.Walls
