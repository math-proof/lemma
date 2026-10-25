/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSourceTrace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part4
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect_ghost1
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
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
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
  classical
  dsimp only
  let mr := fun e => m (lpReplicaCurrentEdgeReflect G sites e)
  let Kr := lpReplicaReflectCopies G sites m K
  have hsrcR : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) mr) Kr =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
    rw [lpReplicaReflectCopies_sources, hsrc,
      lpReplicaCurrentReflect_offdiagSource G sites i j]
  have hdiscR : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) mr) Kr
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hc
    have hc' : StatMech.Sharpness.RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) mr) Kr
        (lpReplicaCurrentReflect
          (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V))
        (lpReplicaCurrentReflect
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)) := by
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hc
    have horiginal := (lpReplicaReflectCopies_connK G sites m K
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost0).mp hc'
    exact hdisc (StatMech.Sharpness.RandomCurrent.connK_symm _ _ horiginal)
  have hcomp :
      StatMech.Sharpness.RandomCurrent.compOf
          (endsM (lpReplicaCurrentGraph G sites) mr) Kr
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) =
        (StatMech.Sharpness.RandomCurrent.compOf
          (endsM (lpReplicaCurrentGraph G sites) m) K
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)).map
            lpReplicaCurrentReflect.toEmbedding := by
    ext x
    simp only [StatMech.Sharpness.RandomCurrent.mem_compOf,
      Finset.mem_map]
    constructor
    · intro hx
      refine ⟨lpReplicaCurrentReflect x, ?_,
        lpReplicaCurrentReflect_involutive x⟩
      have hreflect := (lpReplicaReflectCopies_connK G sites m K
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
        (lpReplicaCurrentReflect x)).mp
      apply hreflect
      change StatMech.Sharpness.RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) mr) Kr
        lpReplicaCurrentGhost0
        (lpReplicaCurrentReflect (lpReplicaCurrentReflect x))
      rw [lpReplicaCurrentReflect_involutive]
      exact hx
    · rintro ⟨y, hy, hyx⟩
      change lpReplicaCurrentReflect y = x at hyx
      subst x
      have hreflect := (lpReplicaReflectCopies_connK G sites m K
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) y).mpr hy
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hreflect
  have h := lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect
    G sites hsite hij mr Kr hsrcR hdiscR
  dsimp only at h
  rw [hcomp] at h
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let C := StatMech.Sharpness.RandomCurrent.compOf
    (endsM (lpReplicaCurrentGraph G sites) m) K
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
  let X := B ∩ C
  have hB : B.map lpReplicaCurrentReflect.toEmbedding = B :=
    lpReplicaCurrentReflect_offdiagSource G sites i j
  have hX : B ∩ C.map lpReplicaCurrentReflect.toEmbedding =
      X.map lpReplicaCurrentReflect.toEmbedding := by
    rw [Finset.map_inter]
    rw [hB]
  rw [hX] at h
  have hdouble :
      (X.map lpReplicaCurrentReflect.toEmbedding).map
          lpReplicaCurrentReflect.toEmbedding = X := by
    ext x
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
      change lpReplicaCurrentReflect z = y at hzy
      change lpReplicaCurrentReflect y = x at hyx
      subst y
      rw [lpReplicaCurrentReflect_involutive] at hyx
      simpa [← hyx] using hz
    · intro hx
      refine ⟨lpReplicaCurrentReflect x, ?_,
        lpReplicaCurrentReflect_involutive x⟩
      exact ⟨x, hx, rfl⟩
  have hbalanced :
      X.map lpReplicaCurrentReflect.toEmbedding ∆
          (X.map lpReplicaCurrentReflect.toEmbedding).map
            lpReplicaCurrentReflect.toEmbedding =
        X ∆ X.map lpReplicaCurrentReflect.toEmbedding := by
    rw [hdouble, symmDiff_comm]
  simpa only [B, C, X, hbalanced] using h


end
end StatMech.Ising
