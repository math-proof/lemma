/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneCore.Part3
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge
open MeasureTheory Set SimpleGraph
open scoped ENNReal


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

theorem finiteOpenAnchors_finite (F : Finset (Sym2 V)) :
    (finiteOpenAnchors F).Finite := by
  have hsub : finiteOpenAnchors F ⊆ ⋃ e ∈ F, {x | x ∈ e} := by
    rintro x ⟨e, he, hxe⟩
    exact Set.mem_biUnion he hxe
  apply Set.Finite.subset _ hsub
  apply Set.Finite.biUnion F.finite_toSet
  intro e _
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hsubxy : {z : V | z ∈ s(x, y)} ⊆ ({x, y} : Set V) := by
        intro z hz
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
          (Sym2.mem_iff.mp hz)
      exact Set.Finite.subset ((Set.finite_singleton y).insert x) hsubxy

theorem PeriodicGraph.adj_forceOpenFinset_cases (P : PeriodicGraph V)
    (F : Finset (Sym2 V)) (omega : ConfigSpace (Sym2 V)) {x y : V}
    (h : (P.openSubgraph (forceOpenFinset F omega)).Adj x y) :
    (P.openSubgraph omega).Adj x y ∨ s(x, y) ∈ F := by
  rw [P.openSubgraph_adj] at h
  by_cases he : s(x, y) ∈ F
  · exact Or.inr he
  · left
    rw [P.openSubgraph_adj]
    exact ⟨h.1, by simpa [forceOpenFinset, he] using h.2⟩

theorem PeriodicGraph.forceOpen_reachable_anchor (P : PeriodicGraph V)
    (F : Finset (Sym2 V)) (omega : ConfigSpace (Sym2 V)) (x z : V)
    (h : (P.openSubgraph (forceOpenFinset F omega)).Reachable x z) :
    (P.openSubgraph omega).Reachable x z ∨
      ∃ a ∈ finiteOpenAnchors F, (P.openSubgraph omega).Reachable a z := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (SimpleGraph.Reachable.refl x)
  | @tail y z hxy hyz ih =>
      rcases P.adj_forceOpenFinset_cases F omega hyz with hadj | he
      · rcases ih with hxy' | ⟨a, ha, hay⟩
        · exact Or.inl (hxy'.trans hadj.reachable)
        · exact Or.inr ⟨a, ha, hay.trans hadj.reachable⟩
      · exact Or.inr ⟨z, ⟨s(y, z), he, Sym2.mem_mk_right y z⟩,
          SimpleGraph.Reachable.refl z⟩

theorem PeriodicGraph.exists_old_infinite_cluster_in_forceOpen
    (P : PeriodicGraph V) (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V)) (x : V)
    (hinf : (P.cluster (forceOpenFinset F omega) x).Infinite) :
    ∃ a, a ∈ P.cluster (forceOpenFinset F omega) x ∧
      (P.cluster omega a).Infinite := by
  let omega' := forceOpenFinset F omega
  let D := P.cluster omega' x
  let A : Set V := insert x (finiteOpenAnchors F)
  have hAfin : A.Finite := (finiteOpenAnchors_finite F).insert x
  have hcover : D ⊆ ⋃ a ∈ A, P.cluster omega a := by
    intro z hz
    rcases P.forceOpen_reachable_anchor F omega x z hz with hxz | ⟨a, ha, haz⟩
    · exact Set.mem_biUnion (Set.mem_insert x _) hxz
    · exact Set.mem_biUnion (Set.mem_insert_of_mem x ha) haz
  have hcover' : D ⊆ ⋃ a ∈ A, (P.cluster omega a ∩ D) := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (hcover hz)
    exact Set.mem_iUnion₂.mpr ⟨a, ha, hza, hz⟩
  have hpiece : ∃ a ∈ A, (P.cluster omega a ∩ D).Infinite := by
    by_contra h
    simp only [not_exists, not_and, Set.not_infinite] at h
    exact hinf ((hAfin.biUnion h).subset hcover')
  obtain ⟨a, _, hainf⟩ := hpiece
  obtain ⟨w, hwa, hwD⟩ := hainf.nonempty
  refine ⟨w, hwD, ?_⟩
  have haInf : (P.cluster omega a).Infinite :=
    hainf.mono Set.inter_subset_left
  exact (P.cluster_eq_of_reachable omega hwa) ▸ haInf

theorem PeriodicGraph.forceOpen_image_repSet_eq
    (P : PeriodicGraph V) (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V)) :
    (fun a => P.cluster (forceOpenFinset F omega) a) ''
        P.infiniteClusterRepSet omega =
      P.infiniteClusters (forceOpenFinset F omega) := by
  let omega' := forceOpenFinset F omega
  have hle : omega <= omega' := forceOpenFinset_le F omega
  ext D
  simp only [Set.mem_image, PeriodicGraph.infiniteClusters, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.1.mono (P.cluster_mono hle a), a, rfl⟩
  · rintro ⟨hinf, x, rfl⟩
    obtain ⟨w, hwD, hwInf⟩ :=
      P.exists_old_infinite_cluster_in_forceOpen F omega x hinf
    obtain ⟨r, hr, hrmin⟩ :=
      exists_periodicVertexIndex_min (P.cluster omega w)
        ⟨w, P.self_mem_cluster omega w⟩
    refine ⟨r, ⟨?_, ?_⟩, ?_⟩
    · exact (P.cluster_eq_of_reachable omega hr) ▸ hwInf
    · intro y hry
      exact hrmin y (hr.trans hry)
    · have hrw : (P.openSubgraph omega').Reachable r w :=
        P.reachable_mono hle hr.symm
      exact P.cluster_eq_of_reachable omega' (hrw.trans hwD.symm)

theorem PeriodicGraph.numInfiniteClusters_lt_of_merge
    (P : PeriodicGraph V) (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V))
    (hfin : P.numInfiniteClusters omega ≠ ⊤)
    (x y : V) (hx : (P.cluster omega x).Infinite)
    (hy : (P.cluster omega y).Infinite)
    (hne : P.cluster omega x ≠ P.cluster omega y)
    (hmerge : (P.openSubgraph (forceOpenFinset F omega)).Reachable x y) :
    P.numInfiniteClusters (forceOpenFinset F omega) <
      P.numInfiniteClusters omega := by
  let omega' := forceOpenFinset F omega
  have hle : omega <= omega' := forceOpenFinset_le F omega
  have hrepfin : (P.infiniteClusterRepSet omega).Finite := by
    rw [← Set.not_infinite]
    intro hInf
    apply hfin
    rw [P.numInfiniteClusters_eq_repSet_encard]
    exact hInf.encard_eq
  obtain ⟨rx, hrx, hrxmin⟩ :=
    exists_periodicVertexIndex_min (P.cluster omega x)
      ⟨x, P.self_mem_cluster omega x⟩
  obtain ⟨ry, hry, hrymin⟩ :=
    exists_periodicVertexIndex_min (P.cluster omega y)
      ⟨y, P.self_mem_cluster omega y⟩
  have hrxrep : rx ∈ P.infiniteClusterRepSet omega := by
    refine ⟨(P.cluster_eq_of_reachable omega hrx) ▸ hx, ?_⟩
    intro z hrxz
    exact hrxmin z (hrx.trans hrxz)
  have hryrep : ry ∈ P.infiniteClusterRepSet omega := by
    refine ⟨(P.cluster_eq_of_reachable omega hry) ▸ hy, ?_⟩
    intro z hryz
    exact hrymin z (hry.trans hryz)
  have hrxy : rx ≠ ry := by
    intro h
    apply hne
    rw [P.cluster_eq_of_reachable omega hrx,
      P.cluster_eq_of_reachable omega hry, h]
  have hsame : P.cluster omega' rx = P.cluster omega' ry := by
    have h1 : (P.openSubgraph omega').Reachable rx x :=
      P.reachable_mono hle hrx.symm
    have h2 : (P.openSubgraph omega').Reachable y ry :=
      P.reachable_mono hle hry
    exact P.cluster_eq_of_reachable omega' ((h1.trans hmerge).trans h2)
  have hni : ¬ Set.InjOn (fun a => P.cluster omega' a)
      (P.infiniteClusterRepSet omega) := fun hinj =>
    hrxy (hinj hrxrep hryrep hsame)
  have hlhs : P.numInfiniteClusters omega' =
      ((fun a => P.cluster omega' a) ''
        P.infiniteClusterRepSet omega).encard := by
    rw [show omega' = forceOpenFinset F omega from rfl,
      P.forceOpen_image_repSet_eq F omega]
    rfl
  rw [hlhs, P.numInfiniteClusters_eq_repSet_encard]
  exact encard_image_lt_of_not_injOn_periodic hrepfin hni

end StatMech.FK.PeriodicPlanar
