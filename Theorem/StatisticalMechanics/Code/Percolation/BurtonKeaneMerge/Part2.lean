/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BKUniqueness2
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


lemma anchorSites_finite (F : Finset (Sym2 (Site d))) : (anchorSites F).Finite := by
  have hsub : anchorSites F ⊆ ⋃ e ∈ F, {a | a ∈ e} := by
    intro a ha; obtain ⟨e, he, hae⟩ := ha; exact Set.mem_biUnion he hae
  apply Set.Finite.subset _ hsub
  apply Set.Finite.biUnion F.finite_toSet
  intro e _
  induction e with
  | h p q =>
    have h2 : {a : Site d | a ∈ s(p, q)} ⊆ ({p, q} : Set (Site d)) := by
      intro a ha
      simp only [Set.mem_setOf_eq, Sym2.mem_iff] at ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact ha
    exact Set.Finite.subset ((Set.finite_singleton q).insert p) h2


lemma adj_forceOpenFinset_cases (F : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (h : (openSubgraph d (forceOpenFinset F ω)).Adj x y) :
    (openSubgraph d ω).Adj x y ∨ (s(x, y) ∈ F) := by
  rw [openSubgraph_adj] at h
  by_cases hF : s(x, y) ∈ F
  · exact Or.inr hF
  · left
    rw [openSubgraph_adj]
    exact ⟨h.1, by rw [← forceOpenFinset_of_notMem hF ω]; exact h.2⟩


lemma anchor_decomp (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (x z : Site d) (h : Connected d (forceOpenFinset F ω) x z) :
    Connected d ω x z ∨ ∃ a ∈ anchorSites F, Connected d ω a z := by
  unfold Connected at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl connected_rfl
  | @tail b c hxb hbc ih =>
    rcases adj_forceOpenFinset_cases F ω hbc with hadj | hF
    · rcases ih with hxb' | ⟨a, ha, hab⟩
      · exact Or.inl (hxb'.trans (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj))
      · exact Or.inr ⟨a, ha, hab.trans (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj)⟩
    · exact Or.inr ⟨c, ⟨s(b, c), hF, Sym2.mem_mk_right b c⟩, connected_rfl⟩


lemma exists_infinite_omega_cluster_in_D (F : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hD : (cluster d (forceOpenFinset F ω) x).Infinite) :
    ∃ a, a ∈ cluster d (forceOpenFinset F ω) x ∧ (cluster d ω a).Infinite := by
  set ω' := forceOpenFinset F ω with hω'
  set D := cluster d ω' x with hDdef
  set S : Set (Site d) := insert x (anchorSites F) with hS
  have hSfin : S.Finite := (anchorSites_finite F).insert x
  
  have hcover : D ⊆ ⋃ a ∈ S, cluster d ω a := by
    intro z hz
    rw [hDdef, mem_cluster] at hz
    rcases anchor_decomp F ω x z hz with hconn | ⟨a, ha, haz⟩
    · exact Set.mem_biUnion (Set.mem_insert x _) (by rw [mem_cluster]; exact hconn)
    · exact Set.mem_biUnion (Set.mem_insert_of_mem x ha) (by rw [mem_cluster]; exact haz)
  have hcover2 : D ⊆ ⋃ a ∈ S, (cluster d ω a ∩ D) := by
    intro z hz
    obtain ⟨T, hT, hzT⟩ := Set.mem_iUnion₂.mp (hcover hz)
    exact Set.mem_iUnion₂.mpr ⟨T, hT, hzT, hz⟩
  
  have hpiece : ∃ a ∈ S, (cluster d ω a ∩ D).Infinite := by
    by_contra hcon
    simp only [not_exists, not_and, Set.not_infinite] at hcon
    exact hD ((hSfin.biUnion hcon).subset hcover2)
  obtain ⟨a, _, hainf⟩ := hpiece
  obtain ⟨w, hwa, hwD⟩ := hainf.nonempty
  refine ⟨w, hwD, ?_⟩
  have hca : (cluster d ω a).Infinite := hainf.mono Set.inter_subset_left
  rw [mem_cluster] at hwa
  rw [← cluster_eq_of_connected hwa]
  exact hca


theorem forceOpen_image_repSet_eq (F : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    (fun a => cluster d (forceOpenFinset F ω) a) '' (repSet d ω)
      = infiniteClusters d (forceOpenFinset F ω) := by
  set ω' := forceOpenFinset F ω with hω'
  have hle : ω ≤ ω' := forceOpenFinset_le F ω
  ext D
  simp only [Set.mem_image, infiniteClusters, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.1.mono (cluster_mono hle a), a, rfl⟩
  · rintro ⟨hinf, x, rfl⟩
    obtain ⟨w, hwD, hwinf⟩ := exists_infinite_omega_cluster_in_D F ω x hinf
    obtain ⟨r, hr, hmin⟩ := exists_encode_min (cluster d ω w) ⟨w, self_mem_cluster ω w⟩
    rw [mem_cluster] at hr
    refine ⟨r, ⟨?_, ?_⟩, ?_⟩
    · rw [← cluster_eq_of_connected hr]; exact hwinf
    · intro y hry; exact hmin y (by rw [mem_cluster]; exact hr.trans hry)
    · have hrw' : Connected d ω' r w := connected_mono hle hr.symm
      rw [mem_cluster] at hwD
      exact cluster_eq_of_connected (hrw'.trans hwD.symm)


theorem numInfiniteClusters_lt_of_merge
    (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hfin : numInfiniteClusters d ω ≠ ⊤)
    (x y : Site d) (hx : (cluster d ω x).Infinite) (hy : (cluster d ω y).Infinite)
    (hne : cluster d ω x ≠ cluster d ω y)
    (hmerge : Connected d (forceOpenFinset F ω) x y) :
    numInfiniteClusters d (forceOpenFinset F ω) < numInfiniteClusters d ω := by
  set ω' := forceOpenFinset F ω with hω'
  have hle : ω ≤ ω' := forceOpenFinset_le F ω
  
  have hrepfin : (repSet d ω).Finite := by
    rw [← Set.not_infinite]
    intro hinf
    exact hfin (by rw [numInfiniteClusters_eq_repSet_encard]; exact hinf.encard_eq)
  
  obtain ⟨rx, hrx, hminx⟩ := exists_encode_min (cluster d ω x) ⟨x, self_mem_cluster ω x⟩
  obtain ⟨ry, hry, hminy⟩ := exists_encode_min (cluster d ω y) ⟨y, self_mem_cluster ω y⟩
  rw [mem_cluster] at hrx hry
  have hrxrep : rx ∈ repSet d ω :=
    ⟨by rw [← cluster_eq_of_connected hrx]; exact hx,
     fun z hz => hminx z (by rw [mem_cluster]; exact hrx.trans hz)⟩
  have hryrep : ry ∈ repSet d ω :=
    ⟨by rw [← cluster_eq_of_connected hry]; exact hy,
     fun z hz => hminy z (by rw [mem_cluster]; exact hry.trans hz)⟩
  
  have hrxry : rx ≠ ry := by
    intro h
    exact hne (by rw [cluster_eq_of_connected hrx, cluster_eq_of_connected hry, h])
  
  have hpsieq : cluster d ω' rx = cluster d ω' ry := by
    have h1 : Connected d ω' rx x := connected_mono hle hrx.symm
    have h2 : Connected d ω' y ry := connected_mono hle hry
    exact cluster_eq_of_connected ((h1.trans hmerge).trans h2)
  
  have hni : ¬ Set.InjOn (fun a => cluster d ω' a) (repSet d ω) := fun hinj =>
    hrxry (hinj hrxrep hryrep hpsieq)
  
  have hlhs : numInfiniteClusters d ω'
      = ((fun a => cluster d ω' a) '' (repSet d ω)).encard := by
    rw [hω', forceOpen_image_repSet_eq F ω]; rfl
  rw [hlhs, numInfiniteClusters_eq_repSet_encard ω]
  exact encard_image_lt_of_not_injOn hrepfin hni


end Percolation
end StatMech
