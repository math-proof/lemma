/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part9
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaBalancedOrbit
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

theorem lpReplicaRowCopies_partialReflectTagRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectTagRaw G sites m P tag) row =
      lpReplicaPartialReflectCopiesRaw G sites m P
        (lpReplicaRowCopies G sites m tag row) := by
  ext c
  simp [lpReplicaRowCopies, lpReplicaPartialReflectTagRaw,
    lpReplicaPartialReflectCopiesRaw]

theorem lpReplicaCurrentCopies_partialReflectTagRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectTagRaw G sites m P tag) row current =
      lpReplicaPartialReflectCopiesRaw G sites m P
        (lpReplicaCurrentCopies G sites m tag row current) := by
  ext c
  simp [lpReplicaCurrentCopies, lpReplicaPartialReflectTagRaw,
    lpReplicaPartialReflectCopiesRaw]


theorem lpReplicaPartialReflectCopiesRaw_connK_of_disjoint
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P T : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hTP : Disjoint T P) (a b : LPReplicaCurrentVertex V) :
    RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P T) a b <->
      RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m) T a b := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let target := lpReplicaCollisionProfile G sites
    (profileFlux H m (Finset.univ \ P)) (profileFlux H m P)
  let ST := {c : Copy H m // c ∈ T}
  let incl : ST ↪ Copy H m := Function.Embedding.subtype _
  let move : ST ↪ Copy H target :=
    incl.trans (lpReplicaPartialReflectCopyEquivRaw G sites m P).toEmbedding
  let endsT : ST -> Sym2 (LPReplicaCurrentVertex V) := fun c => endsM H m c.1
  have hnot (c : ST) : c.1 ∉ P :=
    Finset.disjoint_left.mp hTP c.2
  have hmove (c : ST) : endsM H target (move c) = endsT c := by
    exact lpReplicaPartialReflectCopyEquivRaw_ends_of_not_mem
      G sites m P c.1 (hnot c)
  have hinclSet : (Finset.univ : Finset ST).map incl = T := by
    ext c
    simp [incl, ST]
  have hmoveSet : (Finset.univ : Finset ST).map move =
      lpReplicaPartialReflectCopiesRaw G sites m P T := by
    calc
      (Finset.univ : Finset ST).map move =
          ((Finset.univ : Finset ST).map incl).map
            (lpReplicaPartialReflectCopyEquivRaw G sites m P).toEmbedding := by
              rw [Finset.map_map]
      _ = T.map
            (lpReplicaPartialReflectCopyEquivRaw G sites m P).toEmbedding := by
              rw [hinclSet]
      _ = lpReplicaPartialReflectCopiesRaw G sites m P T := by
              rfl
  have htarget := randomCurrent_connK_map_embedding endsT (endsM H target)
    move hmove Finset.univ a b
  have htarget' : RandomCurrent.connK (endsM H target)
        (lpReplicaPartialReflectCopiesRaw G sites m P T) a b <->
      RandomCurrent.connK endsT Finset.univ a b := by
    simpa only [hmoveSet] using htarget
  have hsource := randomCurrent_connK_map_embedding endsT (endsM H m)
    incl (fun _ => rfl) Finset.univ a b
  have hsource' : RandomCurrent.connK (endsM H m) T a b <->
      RandomCurrent.connK endsT Finset.univ a b := by
    simpa only [hinclSet] using hsource
  exact htarget'.trans hsource'.symm


theorem lpReplicaPartialReflectCopiesRaw_sources_of_disjoint
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P T : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hTP : Disjoint T P) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites
            (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
            (profileFlux (lpReplicaCurrentGraph G sites) m P)))
        (lpReplicaPartialReflectCopiesRaw G sites m P T) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) T := by
  have hsdiff : T \ P = T := by
    ext c
    simp only [Finset.mem_sdiff]
    constructor
    · exact And.left
    · intro hc
      exact ⟨hc, Finset.disjoint_left.mp hTP hc⟩
  have hinter : T ∩ P = ∅ := by
    exact Finset.disjoint_iff_inter_eq_empty.mp hTP
  have hempty : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) ∅ = ∅ := by
    ext x
    simp [RandomCurrent.mem_sources, RandomCurrent.degK]
  rw [lpReplicaPartialReflectCopiesRaw_sources, hsdiff, hinter]
  rw [hempty]
  simp


theorem lpReplicaRowGate_partialReflect_trueComponent
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m ∅ B tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag true
    let P := edgeComponent e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let C := RandomCurrent.compOf e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      ∅ (lpReplicaPartialReflectSource B C)
      (lpReplicaPartialReflectTagRaw G sites m P tag) := by
  classical
  dsimp only
  unfold LPReplicaRowGate at hgate ⊢
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let C := RandomCurrent.compOf e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hPsub : P ⊆ K := by
    intro c hc
    change c ∈ edgeComponent e K lpReplicaCurrentGhost0 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hrows0 : Disjoint
      (lpReplicaRowCopies G sites m tag false)
      (lpReplicaRowCopies G sites m tag true) := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc0 hc1
    exact Bool.false_ne_true (hc0.symm.trans hc1)
  have hrows : Disjoint
      (lpReplicaRowCopies G sites m tag false) K := by
    simpa only [K] using hrows0
  have hrow0P : Disjoint
      (lpReplicaRowCopies G sites m tag false) P :=
    hrows.mono Finset.Subset.rfl hPsub
  have hcurrent0P (current : Bool) : Disjoint
      (lpReplicaCurrentCopies G sites m tag false current) P :=
    hrow0P.mono
      (lpReplicaCurrentCopies_subset_rowCopies G sites m tag false current)
      Finset.Subset.rfl
  have hcurrent1 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag true current ⊆ K :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag true current
  have hsrc1 (current : Bool) :
      RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites)
            (lpReplicaCollisionProfile G sites
              (profileFlux (lpReplicaCurrentGraph G sites) m
                (Finset.univ \ P))
              (profileFlux (lpReplicaCurrentGraph G sites) m P)))
          (lpReplicaPartialReflectCopiesRaw G sites m P
            (lpReplicaCurrentCopies G sites m tag true current)) =
        lpReplicaPartialReflectSource
          (RandomCurrent.sources e
            (lpReplicaCurrentCopies G sites m tag true current)) C := by
    exact lpReplicaPartialReflect_rowComponent_subconfig_sources
      G sites m K
        (lpReplicaCurrentCopies G sites m tag true current)
        (hcurrent1 current) lpReplicaCurrentGhost0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lpReplicaCurrentCopies_partialReflectTagRaw]
    rw [lpReplicaPartialReflectCopiesRaw_sources_of_disjoint
      G sites m P _ (hcurrent0P false), hgate.1]
  · rw [lpReplicaCurrentCopies_partialReflectTagRaw]
    rw [lpReplicaPartialReflectCopiesRaw_sources_of_disjoint
      G sites m P _ (hcurrent0P true), hgate.2.1]
  · rw [lpReplicaRowCopies_partialReflectTagRaw]
    exact fun hconn => hgate.2.2.1
      ((lpReplicaPartialReflectCopiesRaw_connK_of_disjoint
        G sites m P _ hrow0P _ _).mp hconn)
  · rw [lpReplicaCurrentCopies_partialReflectTagRaw, hsrc1 false,
      hgate.2.2.2.1]
  · rw [lpReplicaCurrentCopies_partialReflectTagRaw, hsrc1 true,
      hgate.2.2.2.2.1]
    simp [lpReplicaPartialReflectSource]
  · rw [lpReplicaRowCopies_partialReflectTagRaw]
    exact lpReplicaPartialReflect_rowComponent_ghost_disconn
      G sites m K hgate.2.2.2.2.2


theorem lpReplicaRowGate_partialReflect_offdiag
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag true
    let P := edgeComponent e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (LPReplicaRowGate G sites target ∅ Si
          (lpReplicaPartialReflectTagRaw G sites m P tag) ∧
        (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T) ∨
      (LPReplicaRowGate G sites target ∅ Sj
          (lpReplicaPartialReflectTagRaw G sites m P tag) ∧
        (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T) := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let C := RandomCurrent.compOf e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hrows := lpReplicaRowGate_rowSources G sites m ∅ (Si ∆ Sj ∆ T)
    tag hgate
  have hgateFields := hgate
  unfold LPReplicaRowGate at hgateFields
  have htransport := lpReplicaRowGate_partialReflect_trueComponent
    G sites m (Si ∆ Sj ∆ T) tag hgate
  have halloc := lpReplicaOffdiagRowComponent_partialReflectAllocation
    G sites hsite hij m K hrows.2 hgateFields.2.2.2.2.2
  dsimp only [Si, Sj, T, C, K, e] at htransport halloc ⊢
  rcases halloc with halloc | halloc
  · left
    have hcomplement := halloc.2
    rw [halloc.1] at hcomplement
    refine ⟨?_, hcomplement⟩
    simpa only [halloc.1] using htransport
  · right
    have hcomplement := halloc.2
    rw [halloc.1] at hcomplement
    refine ⟨?_, hcomplement⟩
    simpa only [halloc.1] using htransport


end
end StatMech.Ising
