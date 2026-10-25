/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part8
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaPartialReflectCopiesRaw_selected_profileFlux
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    profileFlux (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopiesRaw G sites m P P) =
      fun e => profileFlux (lpReplicaCurrentGraph G sites) m P
        (lpReplicaCurrentEdgeReflect G sites e) := by
  funext e
  unfold profileFlux lpReplicaPartialReflectCopiesRaw
  let E := (lpReplicaPartialReflectCopyEquivRaw G sites m P).toEmbedding
  change #((P.map E).filter (fun i => i.1 = e)) =
    #(P.filter (fun i => i.1 = lpReplicaCurrentEdgeReflect G sites e))
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c hc
  change (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1 = e <->
    c.1 = lpReplicaCurrentEdgeReflect G sites e
  rw [lpReplicaPartialReflectCopyEquivRaw_edge, if_pos hc]
  constructor
  · intro h
    have hr := congrArg (lpReplicaCurrentEdgeReflect G sites) h
    rw [lpReplicaCurrentEdgeReflect_involutive G sites c.1] at hr
    exact hr
  · intro h
    have hr := congrArg (lpReplicaCurrentEdgeReflect G sites) h
    rw [lpReplicaCurrentEdgeReflect_involutive G sites e] at hr
    exact hr


theorem lpReplicaPartialReflectCopiesRaw_selected_profile_inverse
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let P' := lpReplicaPartialReflectCopiesRaw G sites m P P
    lpReplicaPartialReflectProfile G sites target
      (profileFlux (lpReplicaCurrentGraph G sites) target P') = m := by
  dsimp only
  rw [lpReplicaPartialReflectCopiesRaw_selected_profileFlux,
    lpReplicaCollisionProfile_compl_eq_partialReflectProfile]
  exact lpReplicaPartialReflectProfile_involutive G sites m _
    (profileFlux_le (lpReplicaCurrentGraph G sites) m P)

theorem lpReplicaPartialReflectCopyEquivRaw_ends_of_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) (hc : c ∈ P) :
    endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) =
      Sym2.map lpReplicaCurrentReflect
        (endsM (lpReplicaCurrentGraph G sites) m c) := by
  change (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1.1 =
    Sym2.map lpReplicaCurrentReflect c.1.1
  rw [lpReplicaPartialReflectCopyEquivRaw_edge, if_pos hc,
    lpReplicaCurrentEdgeReflect_val]

theorem lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) (hc : c ∉ P) :
    endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) =
      endsM (lpReplicaCurrentGraph G sites) m c := by
  change (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1.1 = c.1.1
  rw [lpReplicaPartialReflectCopyEquivRaw_edge, if_neg hc]


theorem lpReplicaPartialReflectCopiesRaw_selected_degK
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (x : LPReplicaCurrentVertex V) :
    RandomCurrent.degK
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P P)
        (lpReplicaCurrentReflect x) =
      RandomCurrent.degK
        (endsM (lpReplicaCurrentGraph G sites) m) P x := by
  unfold RandomCurrent.degK lpReplicaPartialReflectCopiesRaw
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c hc
  change lpReplicaCurrentReflect x ∈
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) <->
    x ∈ endsM (lpReplicaCurrentGraph G sites) m c
  rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_mem G sites m P c hc,
    Sym2.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := lpReplicaCurrentReflect.injective hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩


theorem lpReplicaPartialReflectCopiesRaw_selected_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P P) =
      (RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) m) P).map
          lpReplicaCurrentReflect.toEmbedding := by
  ext y
  have hy := lpReplicaCurrentReflect_involutive (V := V) y
  rw [<- hy]
  simp only [RandomCurrent.mem_sources,
    lpReplicaPartialReflectCopiesRaw_selected_degK]
  simp


theorem lpReplicaPartialReflectCopiesRaw_compl_degK
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (x : LPReplicaCurrentVertex V) :
    RandomCurrent.degK
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P)) x =
      RandomCurrent.degK (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ \ P) x := by
  unfold RandomCurrent.degK lpReplicaPartialReflectCopiesRaw
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c hc
  have hcP : c ∉ P := (Finset.mem_sdiff.mp hc).2
  change x ∈ endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      (lpReplicaPartialReflectCopyEquivRaw G sites m P c) <->
    x ∈ endsM (lpReplicaCurrentGraph G sites) m c
  rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem G sites m P c hcP]


theorem lpReplicaPartialReflectCopiesRaw_compl_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P)) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ \ P) := by
  ext x
  simp only [RandomCurrent.mem_sources,
    lpReplicaPartialReflectCopiesRaw_compl_degK]


theorem lpReplicaPartialReflectCopiesRaw_compl_union_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P) ∪
        lpReplicaPartialReflectCopiesRaw G sites m P P = Finset.univ := by
  unfold lpReplicaPartialReflectCopiesRaw
  rw [<- Finset.map_union,
    Finset.sdiff_union_of_subset (Finset.subset_univ P)]
  ext c
  simp

theorem lpReplicaPartialReflectCopiesRaw_compl_disjoint_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Disjoint
      (lpReplicaPartialReflectCopiesRaw G sites m P (Finset.univ \ P))
      (lpReplicaPartialReflectCopiesRaw G sites m P P) := by
  unfold lpReplicaPartialReflectCopiesRaw
  rw [Finset.disjoint_map]
  exact Finset.sdiff_disjoint


theorem lpReplicaPartialReflectCopiesRaw_univ_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P))) Finset.univ =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (Finset.univ \ P) ∆
        (RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) P).map
            lpReplicaCurrentReflect.toEmbedding := by
  rw [<- lpReplicaPartialReflectCopiesRaw_compl_union_selected G sites m P,
    sources_union_of_disjoint
      (lpReplicaPartialReflectCopiesRaw_compl_disjoint_selected G sites m P),
    lpReplicaPartialReflectCopiesRaw_compl_sources,
    lpReplicaPartialReflectCopiesRaw_selected_sources]


theorem lpReplicaPartialReflect_rootComponent_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A : Finset (LPReplicaCurrentVertex V))
    (root : LPReplicaCurrentVertex V)
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) = A) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ root
    let C := RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ root
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P))) Finset.univ =
      lpReplicaPartialReflectSource A C := by
  dsimp only
  classical
  classical
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let P := edgeComponent e Finset.univ root
  let C := RandomCurrent.compOf e Finset.univ root
  have hPsub : P ⊆ (Finset.univ :
      Finset (Copy (lpReplicaCurrentGraph G sites) m)) := Finset.subset_univ _
  have hPsrc : RandomCurrent.sources e P = A ∩ C := by
    rw [sources_edgeComponent, hsrc]
  have hcompl : RandomCurrent.sources e (Finset.univ \ P) = A \ C := by
    rw [sources_sdiff_of_subset hPsub, hsrc, hPsrc]
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [lpReplicaPartialReflectCopiesRaw_univ_sources, hcompl, hPsrc]
  rfl


theorem lpReplicaPartialReflectCopiesRaw_sdiff_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P K : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (K \ P)) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (K \ P) := by
  ext x
  simp only [RandomCurrent.mem_sources]
  unfold RandomCurrent.degK lpReplicaPartialReflectCopiesRaw
  rw [Finset.filter_map, Finset.card_map]
  change Odd #((K \ P).filter (fun c => x ∈
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c))) <->
    Odd #((K \ P).filter (fun c =>
      x ∈ endsM (lpReplicaCurrentGraph G sites) m c))
  have hfilter :
      (K \ P).filter (fun c => x ∈
        endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P))
          (lpReplicaPartialReflectCopyEquivRaw G sites m P c)) =
        (K \ P).filter (fun c =>
          x ∈ endsM (lpReplicaCurrentGraph G sites) m c) := by
    apply Finset.filter_congr
    intro c hc
    have hcP : c ∉ P := (Finset.mem_sdiff.mp hc).2
    rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem
      G sites m P c hcP]
  rw [hfilter]


theorem lpReplicaPartialReflectCopiesRaw_sdiff_union_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hPK : P ⊆ K) :
    lpReplicaPartialReflectCopiesRaw G sites m P (K \ P) ∪
        lpReplicaPartialReflectCopiesRaw G sites m P P =
      lpReplicaPartialReflectCopiesRaw G sites m P K := by
  unfold lpReplicaPartialReflectCopiesRaw
  rw [<- Finset.map_union, Finset.sdiff_union_of_subset hPK]

theorem lpReplicaPartialReflectCopiesRaw_sdiff_disjoint_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P K : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Disjoint
      (lpReplicaPartialReflectCopiesRaw G sites m P (K \ P))
      (lpReplicaPartialReflectCopiesRaw G sites m P P) := by
  unfold lpReplicaPartialReflectCopiesRaw
  rw [Finset.disjoint_map]
  exact Finset.sdiff_disjoint


theorem lpReplicaPartialReflect_rowComponent_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (A : Finset (LPReplicaCurrentVertex V))
    (root : LPReplicaCurrentVertex V)
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K = A) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) K root
    let C := RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K root
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P K) =
      lpReplicaPartialReflectSource A C := by
  dsimp only
  classical
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let P := edgeComponent e K root
  let C := RandomCurrent.compOf e K root
  have hPsub : P ⊆ K := by
    intro c hc
    change c ∈ edgeComponent e K root at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hPsrc : RandomCurrent.sources e P = A ∩ C := by
    rw [sources_edgeComponent, hsrc]
  have houtside : RandomCurrent.sources e (K \ P) = A \ C := by
    rw [sources_sdiff_of_subset hPsub, hsrc, hPsrc]
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [<- lpReplicaPartialReflectCopiesRaw_sdiff_union_selected
      G sites m P K hPsub,
    sources_union_of_disjoint
      (lpReplicaPartialReflectCopiesRaw_sdiff_disjoint_selected
        G sites m P K),
    lpReplicaPartialReflectCopiesRaw_sdiff_sources,
    lpReplicaPartialReflectCopiesRaw_selected_sources,
    houtside, hPsrc]
  rfl


theorem lpReplicaPartialReflect_rowComponent_ghost_disconn
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hdisc : Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)))
      (lpReplicaPartialReflectCopiesRaw G sites m P K)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
  dsimp only
  classical
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  change Not (RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P)))
    (lpReplicaPartialReflectCopiesRaw G sites m P K)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
  apply not_connK_of_no_incident
    (show (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
      lpReplicaCurrentGhost1 by simp
        [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])
  intro d hd hdg0
  rw [lpReplicaPartialReflectCopiesRaw] at hd
  obtain ⟨c, hcK, rfl⟩ := Finset.mem_map.mp hd
  by_cases hcP : c ∈ P
  · change lpReplicaCurrentGhost0 ∈
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) at hdg0
    rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_mem
      G sites m P c hcP, Sym2.mem_map] at hdg0
    obtain ⟨x, hxc, hxg0⟩ := hdg0
    have hx : x = (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) := by
      apply lpReplicaCurrentReflect.injective
      simpa [lpReplicaCurrentGhost1] using hxg0
    subst x
    change c ∈ edgeComponent e K lpReplicaCurrentGhost0 at hcP
    rw [edgeComponent, Finset.mem_filter] at hcP
    exact hdisc (hcP.2 lpReplicaCurrentGhost1 hxc)
  · change lpReplicaCurrentGhost0 ∈
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopyEquivRaw G sites m P c) at hdg0
    rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem
      G sites m P c hcP] at hdg0
    exact hcP (mem_edgeComponent_of_endpoint hcK hdg0)


theorem lpReplicaOffdiagRowComponent_partialReflectAllocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
    let C := RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    let P := lpReplicaPartialReflectSource (Si ∆ Sj ∆ T) C
    (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨
      (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let p := profileFlux H m K
  have hsrcp : RandomCurrent.sources (endsM H p)
      (Finset.univ : Finset (Copy H p)) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    rw [StatMech.Sharpness.FluxEdgeCopy.sources_eq,
      profileFlux_univ]
    rw [<- StatMech.Sharpness.FluxEdgeCopy.sources_eq H m K]
    exact hsrc
  have hdiscp : Not (RandomCurrent.connK (endsM H p)
      (Finset.univ : Finset (Copy H p))
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
    intro hpconn
    apply hdisc
    rw [StatMech.Sharpness.FluxEdgeCopy.connK_iff,
      profileFlux_univ] at hpconn
    rw [StatMech.Sharpness.FluxEdgeCopy.connK_iff]
    exact hpconn
  have halloc := lpReplicaOffdiagComponent_partialReflectAllocation
    G sites hsite hij p hsrcp hdiscp
  have hcomp : RandomCurrent.compOf (endsM H p) Finset.univ
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) =
    RandomCurrent.compOf (endsM H m) K lpReplicaCurrentGhost0 := by
    ext x
    simp only [RandomCurrent.mem_compOf]
    rw [StatMech.Sharpness.FluxEdgeCopy.connK_iff,
      profileFlux_univ,
      StatMech.Sharpness.FluxEdgeCopy.connK_iff]
  dsimp only at halloc
  rw [hcomp] at halloc
  exact halloc


theorem lpReplicaOffdiagRowComponent_partialReflectTargetAllocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let Q := RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)))
      (lpReplicaPartialReflectCopiesRaw G sites m P K)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (Q = Si ∧ (Si ∆ Sj ∆ T) ∆ Q = Sj ∆ T) ∨
      (Q = Sj ∧ (Si ∆ Sj ∆ T) ∆ Q = Si ∆ T) := by
  dsimp only
  have hQ := lpReplicaPartialReflect_rowComponent_sources
    G sites m K
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) hsrc
  have halloc := lpReplicaOffdiagRowComponent_partialReflectAllocation
    G sites hsite hij m K hsrc hdisc
  dsimp only at hQ halloc
  rw [hQ]
  exact halloc


theorem lpReplicaPartialReflectCopiesRaw_inter_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P T : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P)) =
      (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (T ∩ P)).map lpReplicaCurrentReflect.toEmbedding := by
  ext y
  have hdeg : RandomCurrent.degK
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P)) y =
      RandomCurrent.degK (endsM (lpReplicaCurrentGraph G sites) m)
        (T ∩ P) (lpReplicaCurrentReflect y) := by
    unfold RandomCurrent.degK lpReplicaPartialReflectCopiesRaw
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    apply Finset.filter_congr
    intro c hc
    have hcP : c ∈ P := (Finset.mem_inter.mp hc).2
    change y ∈ endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P))
          (lpReplicaPartialReflectCopyEquivRaw G sites m P c) <->
        lpReplicaCurrentReflect y ∈
          endsM (lpReplicaCurrentGraph G sites) m c
    rw [lpReplicaPartialReflectCopyEquivRaw_ends_of_mem G sites m P c hcP,
      Sym2.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hx' : x = lpReplicaCurrentReflect y :=
        lpReplicaCurrentReflect.injective
          (hxy.trans (lpReplicaCurrentReflect_involutive y).symm)
      simpa [hx'] using hx
    · intro hy
      exact ⟨lpReplicaCurrentReflect y, hy,
        lpReplicaCurrentReflect_involutive y⟩
  simp only [RandomCurrent.mem_sources, hdeg, Finset.mem_map]
  constructor
  · intro hy
    exact ⟨lpReplicaCurrentReflect y, hy,
      lpReplicaCurrentReflect_involutive y⟩
  · rintro ⟨x, hx, hxy⟩
    have hx' : x = lpReplicaCurrentReflect y :=
      lpReplicaCurrentReflect.injective
        (hxy.trans (lpReplicaCurrentReflect_involutive y).symm)
    simpa [hx'] using hx


theorem lpReplicaPartialReflectCopiesRaw_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P T : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P T) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (T \ P) ∆
        (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (T ∩ P)).map lpReplicaCurrentReflect.toEmbedding := by
  have hunion : T \ P ∪ T ∩ P = T := by
    ext c
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisj : Disjoint (T \ P) (T ∩ P) := by
    rw [Finset.disjoint_left]
    intro c hc hcp
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_inter.mp hcp).2
  have hraw : lpReplicaPartialReflectCopiesRaw G sites m P T =
      lpReplicaPartialReflectCopiesRaw G sites m P (T \ P) ∪
        lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P) := by
    unfold lpReplicaPartialReflectCopiesRaw
    rw [<- Finset.map_union, hunion]
  have hrawdisj : Disjoint
      (lpReplicaPartialReflectCopiesRaw G sites m P (T \ P))
      (lpReplicaPartialReflectCopiesRaw G sites m P (T ∩ P)) := by
    unfold lpReplicaPartialReflectCopiesRaw
    exact (Finset.disjoint_map _).2 hdisj
  rw [hraw,
    sources_union_of_disjoint hrawdisj,
    lpReplicaPartialReflectCopiesRaw_sdiff_sources,
    lpReplicaPartialReflectCopiesRaw_inter_sources]


theorem lpReplicaPartialReflect_rowComponent_subconfig_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K T : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hTK : T ⊆ K)
    (root : LPReplicaCurrentVertex V) :
    let P := edgeComponent
      (endsM (lpReplicaCurrentGraph G sites) m) K root
    let C := RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K root
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P T) =
      lpReplicaPartialReflectSource
        (RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) T) C := by
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let P := edgeComponent e K root
  let C := RandomCurrent.compOf e K root
  have hinter : RandomCurrent.sources e (T ∩ P) =
      RandomCurrent.sources e T ∩ C := by
    exact sources_inter_edgeComponent hTK root
  have houtside : RandomCurrent.sources e (T \ P) =
      RandomCurrent.sources e T \ C := by
    have hsdiff : T \ P = T \ (T ∩ P) := by
      ext c
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [hsdiff, sources_sdiff_of_subset Finset.inter_subset_left, hinter]
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [lpReplicaPartialReflectCopiesRaw_sources, houtside, hinter]
  rfl


theorem lpReplicaReflectCopies_edgeComponent
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (root : LPReplicaCurrentVertex V) :
    lpReplicaReflectCopies G sites m
        (edgeComponent
          (endsM (lpReplicaCurrentGraph G sites) m) K root) =
      edgeComponent
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m K)
        (lpReplicaCurrentReflect root) := by
  ext c
  let R := lpReplicaReflectCopyEquiv G sites m
  let d := R.symm c
  have hdc : R d = c := R.apply_symm_apply c
  rw [mem_lpReplicaReflectCopies]
  unfold edgeComponent
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hdK, hdconn⟩
    refine ⟨(mem_lpReplicaReflectCopies G sites m K c).2 hdK, ?_⟩
    intro y hy
    rw [← hdc] at hy
    rw [lpReplicaReflectCopyEquiv_ends, Sym2.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (lpReplicaReflectCopies_connK G sites m K root x).2
      (hdconn x hx)
  · rintro ⟨hcK, hcconn⟩
    refine ⟨(mem_lpReplicaReflectCopies G sites m K c).1 hcK, ?_⟩
    intro x hx
    have hy : lpReplicaCurrentReflect x ∈
        endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) c := by
      rw [← hdc]
      exact (lpReplicaReflectCopyEquiv_incident G sites m d x).2 hx
    exact (lpReplicaReflectCopies_connK G sites m K root x).1
      (hcconn (lpReplicaCurrentReflect x) hy)


theorem lpReplicaReflectCopies_edgeComponent_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (root : LPReplicaCurrentVertex V) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (edgeComponent
          (endsM (lpReplicaCurrentGraph G sites)
            (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
          (lpReplicaReflectCopies G sites m K)
          (lpReplicaCurrentReflect root)) =
      (RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) m)
        (edgeComponent
          (endsM (lpReplicaCurrentGraph G sites) m) K root)).map
        lpReplicaCurrentReflect.toEmbedding := by
  rw [← lpReplicaReflectCopies_edgeComponent]
  exact lpReplicaReflectCopies_sources G sites m _

end
end StatMech.Ising
