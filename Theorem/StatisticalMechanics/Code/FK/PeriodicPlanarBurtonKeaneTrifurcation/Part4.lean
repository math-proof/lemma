/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part4
open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


theorem PeriodicGraph.orbitShell_subset_source_image
    (P : PeriodicGraph V) (n c : Nat) :
    P.orbitShell n c ⊆
      (P.orbitShellSource n c).image (fun zu => P.shift zu.1 zu.2) := by
  intro x hx
  rw [PeriodicGraph.orbitShell, Finset.mem_sdiff] at hx
  rw [P.mem_orbitBox_iff] at hx
  obtain ⟨z, hz, u, hu, rfl⟩ := hx.1
  apply Finset.mem_image.mpr
  refine ⟨(z, u), ?_, rfl⟩
  rw [PeriodicGraph.orbitShellSource, Finset.mem_product, Finset.mem_sdiff,
    Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
  refine ⟨⟨hz, ?_⟩, hu⟩
  intro hzsmall
  apply hx.2
  rw [P.mem_orbitBox_iff]
  exact ⟨z, hzsmall, u, hu, rfl⟩

theorem PeriodicGraph.orbitShell_card_le
    (P : PeriodicGraph V) (n c : Nat) :
    (P.orbitShell n c).card <=
      (((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) *
        P.fundamentalDomain.card) := by
  calc
    (P.orbitShell n c).card <=
        ((P.orbitShellSource n c).image (fun zu => P.shift zu.1 zu.2)).card :=
      Finset.card_le_card (P.orbitShell_subset_source_image n c)
    _ <= (P.orbitShellSource n c).card := Finset.card_image_le
    _ = (((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) *
        P.fundamentalDomain.card) := by
      rw [PeriodicGraph.orbitShellSource, Finset.card_product,
        Finset.card_sdiff_of_subset]
      · rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF,
          ← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
      · intro z hz
        rw [Set.Finite.mem_toFinset] at hz ⊢
        exact box_mono 2 (Nat.le_add_right n c) hz

theorem PeriodicPlaneEmbedding.orbitBox_card_ge_quadratic
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P) (n : Nat) :
    (2 * n + 1) ^ 2 <= (P.orbitBox n).card := by
  let u := P.root
  let Z := (box_finite 2 n).toFinset
  have hinj : Function.Injective (fun z : Site 2 => P.shift z u) := by
    intro z w hzw
    have hv := congrArg (fun x => E.vertex x) hzw
    change E.vertex (P.shift z u) = E.vertex (P.shift w u) at hv
    rw [E.vertex_shift, E.vertex_shift] at hv
    apply E.period_injective
    exact add_left_cancel hv
  have hsub : Z.image (fun z => P.shift z u) ⊆ P.orbitBox n := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [P.mem_orbitBox_iff]
    exact ⟨z, by simpa [Z] using hz, u, P.root_mem_fundamentalDomain, rfl⟩
  calc
    (2 * n + 1) ^ 2 = Z.card := by
      rw [show Z = (box_finite 2 n).toFinset from rfl,
        ← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
    _ = (Z.image (fun z => P.shift z u)).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ <= (P.orbitBox n).card := Finset.card_le_card hsub

omit [Countable V] in
theorem removeVertex_le (x : V) (omega : ConfigSpace (Sym2 V)) :
    removeVertex x omega <= omega := by
  intro e
  by_cases hx : x ∈ e <;> simp [removeVertex, hx]

omit [Countable V] in
theorem PeriodicGraph.openSubgraph_removeVertex_le
    (P : PeriodicGraph V) (x : V) (omega : ConfigSpace (Sym2 V)) :
    P.openSubgraph (removeVertex x omega) <= P.openSubgraph omega :=
  P.openSubgraph_mono (removeVertex_le x omega)

theorem PeriodicGraph.trifurcation_orbitShell_witnesses
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (n : Nat) {x : V} (hx : x ∈ P.orbitBox n)
    (htrif : P.IsTrifurcation omega x) :
    ∃ t1 t2 t3 : V,
      t1 ∈ P.orbitShell n P.neighborOrbitRadius ∧
      t2 ∈ P.orbitShell n P.neighborOrbitRadius ∧
      t3 ∈ P.orbitShell n P.neighborOrbitRadius ∧
      x ≠ t1 ∧ x ≠ t2 ∧ x ≠ t3 ∧
      (P.openSubgraph omega).Reachable x t1 ∧
      (P.openSubgraph omega).Reachable x t2 ∧
      (P.openSubgraph omega).Reachable x t3 ∧
      ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t1 t2 ∧
      ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t1 t3 ∧
      ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t2 t3 := by
  obtain ⟨a1, a2, a3, ha1, ha2, ha3, hi1, hi2, hi3,
    hd12, hd13, hd23⟩ := htrif
  let cut := P.openSubgraph (removeVertex x omega)
  let S : Set V := P.orbitBox (n + P.neighborOrbitRadius)
  have arm_mem (a : V) (ha : (P.openSubgraph omega).Adj x a) : a ∈ S := by
    exact P.neighbor_mem_orbitBox_add hx ha.1
  have arm_exit (a : V) (ha : a ∈ S)
      (hi : (P.cluster (removeVertex x omega) a).Infinite) :
      ∃ t : V, t ∈ P.orbitShell n P.neighborOrbitRadius ∧
        cut.Reachable a t := by
    have hout : ∃ z : V, z ∉ S ∧ cut.Reachable a z := by
      by_contra h
      push Not at h
      have hsub : P.cluster (removeVertex x omega) a ⊆ S := by
        intro z hz
        by_contra hzS
        exact h z hzS hz
      exact hi ((P.orbitBox (n + P.neighborOrbitRadius)).finite_toSet.subset hsub)
    obtain ⟨z, hzS, haz⟩ := hout
    obtain ⟨t, hat, w, htw, hwS⟩ :=
      reachable_induce_innerBoundary cut S ha hzS haz
    have hatFull : cut.Reachable a t.1 :=
      hat.map (SimpleGraph.Embedding.induce S).toHom
    refine ⟨t.1, ?_, hatFull⟩
    rw [PeriodicGraph.orbitShell, Finset.mem_sdiff]
    refine ⟨t.2, ?_⟩
    intro htn
    have hwmem := P.neighbor_mem_orbitBox_add htn htw.1
    exact hwS hwmem
  obtain ⟨t1, ht1shell, ht1⟩ := arm_exit a1 (arm_mem a1 ha1) hi1
  obtain ⟨t2, ht2shell, ht2⟩ := arm_exit a2 (arm_mem a2 ha2) hi2
  obtain ⟨t3, ht3shell, ht3⟩ := arm_exit a3 (arm_mem a3 ha3) hi3
  have hcutLe : cut <= P.openSubgraph omega :=
    P.openSubgraph_removeVertex_le x omega
  have hreach1 : (P.openSubgraph omega).Reachable x t1 :=
    ha1.reachable.trans (ht1.mono hcutLe)
  have hreach2 : (P.openSubgraph omega).Reachable x t2 :=
    ha2.reachable.trans (ht2.mono hcutLe)
  have hreach3 : (P.openSubgraph omega).Reachable x t3 :=
    ha3.reachable.trans (ht3.mono hcutLe)
  have hdeleteEq : (P.openSubgraph omega).deleteIncidenceSet x = cut := by
    ext a b
    simp only [SimpleGraph.deleteIncidenceSet_adj,
      PeriodicGraph.openSubgraph_adj, cut, removeVertex]
    by_cases hxa : x = a
    · subst a
      simp
    by_cases hxb : x = b
    · subst b
      simp
    have hxmem : x ∉ s(a, b) := by
      simpa only [Sym2.mem_iff, not_or] using ⟨hxa, hxb⟩
    have hax : a ≠ x := Ne.symm hxa
    have hbx : b ≠ x := Ne.symm hxb
    simp [hxa, hxb, hax, hbx, hxmem]
  have hne (t : V) (ht : t ∈ P.orbitShell n P.neighborOrbitRadius) : x ≠ t := by
    intro hxt
    subst t
    exact (Finset.mem_sdiff.mp ht).2 hx
  refine ⟨t1, t2, t3, ht1shell, ht2shell, ht3shell,
    hne t1 ht1shell, hne t2 ht2shell, hne t3 ht3shell,
    hreach1, hreach2, hreach3, ?_, ?_, ?_⟩
  · rw [hdeleteEq]
    intro h
    exact hd12 (ht1.trans (h.trans ht2.symm))
  · rw [hdeleteEq]
    intro h
    exact hd13 (ht1.trans (h.trans ht3.symm))
  · rw [hdeleteEq]
    intro h
    exact hd23 (ht2.trans (h.trans ht3.symm))

end StatMech.FK.PeriodicPlanar
