/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated.Part2
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplica_source_symmDiff_partialReflectSource
    (A C : Finset (LPReplicaCurrentVertex V)) :
    A ∆ lpReplicaPartialReflectSource A C =
      (A ∩ C) ∆
        (A ∩ C).map lpReplicaCurrentReflect.toEmbedding := by
  ext x
  simp only [lpReplicaPartialReflectSource, Finset.mem_symmDiff,
    Finset.mem_sdiff, Finset.mem_inter, Finset.mem_map]
  have hmap :
      (∃ a, (a ∈ A ∧ a ∈ C) ∧
          (lpReplicaCurrentReflect.toEmbedding :
            LPReplicaCurrentVertex V ↪ LPReplicaCurrentVertex V) a = x) ↔
        lpReplicaCurrentReflect x ∈ A ∧
          lpReplicaCurrentReflect x ∈ C := by
    constructor
    · rintro ⟨a, ha, hax⟩
      change lpReplicaCurrentReflect a = x at hax
      subst x
      rw [lpReplicaCurrentReflect_involutive (V := V) a]
      exact ha
    · intro hx
      refine ⟨lpReplicaCurrentReflect x, hx, ?_⟩
      exact lpReplicaCurrentReflect_involutive x
  rw [hmap]
  tauto


theorem lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let C := StatMech.Sharpness.RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let X :=
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∩ C
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    ((Si ∆ Sj ∆ T) ∆ Si =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨
      ((Si ∆ Sj ∆ T) ∆ Sj =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
  dsimp only
  let C := StatMech.Sharpness.RandomCurrent.compOf
    (endsM (lpReplicaCurrentGraph G sites) m) K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  have halloc := lpReplicaOffdiagRowComponent_partialReflectAllocation
    G sites hsite hij m K hsrc hdisc
  have hchange := lpReplica_source_symmDiff_partialReflectSource
    B C
  dsimp only [B, Si, Sj, T, C] at halloc hchange ⊢
  rcases halloc with halloc | halloc
  · left
    calc
      _ = (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) ∆
          lpReplicaPartialReflectSource
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1)
            (StatMech.Sharpness.RandomCurrent.compOf
              (endsM (lpReplicaCurrentGraph G sites) m) K
              lpReplicaCurrentGhost0) :=
        congrArg (fun Z =>
          (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) ∆ Z) halloc.1.symm
      _ = _ := hchange
  · right
    calc
      _ = (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) ∆
          lpReplicaPartialReflectSource
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1)
            (StatMech.Sharpness.RandomCurrent.compOf
              (endsM (lpReplicaCurrentGraph G sites) m) K
              lpReplicaCurrentGhost0) :=
        congrArg (fun Z =>
          (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) ∆ Z) halloc.1.symm
      _ = _ := hchange

set_option maxHeartbeats 800000 in


theorem exists_lpReplicaOffdiag_missingSource_half
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (∃ X, Sj ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨
      (∃ X, Si ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
  dsimp only
  have h := lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect
    G sites hsite hij m K hsrc hdisc
  rcases h with h | h
  · left
    refine ⟨((lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∩
      StatMech.Sharpness.RandomCurrent.compOf
        (endsM (lpReplicaCurrentGraph G sites) m) K
        lpReplicaCurrentGhost0), ?_⟩
    rw [← h]
    ext x
    simp only [Finset.mem_symmDiff]
    tauto
  · right
    refine ⟨((lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∩
      StatMech.Sharpness.RandomCurrent.compOf
        (endsM (lpReplicaCurrentGraph G sites) m) K
        lpReplicaCurrentGhost0), ?_⟩
    rw [← h]
    ext x
    simp only [Finset.mem_symmDiff]
    tauto


theorem lpReplicaPartialReflectTagRaw_toggleRows
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaPartialReflectTagRaw G sites m P
        (lpReplicaToggleRows G sites m P tag) =
      lpReplicaToggleRows G sites
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCopiesRaw G sites m P P)
        (lpReplicaPartialReflectTagRaw G sites m P tag) := by
  funext c
  simp [lpReplicaPartialReflectTagRaw, lpReplicaToggleRows,
    lpReplicaPartialReflectCopiesRaw]


theorem lpReplicaRowComponent_currentTrue_sources_empty
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (row : Bool) (root : LPReplicaCurrentVertex V) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag row
    let P := edgeComponent e K root
    StatMech.Sharpness.RandomCurrent.sources e
      (P.filter fun c => (tag c).2 = true) = ∅ := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag row
  let T := lpReplicaCurrentCopies G sites m tag row true
  have hTsub : T ⊆ K :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag row true
  have hinter : (edgeComponent e K root).filter
      (fun c => (tag c).2 = true) = T ∩ edgeComponent e K root := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · intro h
      refine ⟨?_, h.1⟩
      have hrow : (tag c).1 = row := by
        have hcK : c ∈ K := by
          have hcP := h.1
          rw [edgeComponent, Finset.mem_filter] at hcP
          exact hcP.1
        simp only [K, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at hcK
        exact hcK
      change c ∈ T
      simp only [T, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Prod.ext hrow h.2
    · intro h
      refine ⟨h.2, ?_⟩
      have hc := h.1
      simp only [T, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc
      exact congrArg Prod.snd hc
  rw [hinter, sources_inter_edgeComponent hTsub]
  cases row
  · rw [hgate.2.1]
    simp
  · rw [hgate.2.2.2.2.1]
    simp


end
end StatMech.Ising
