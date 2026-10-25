/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandFamily
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (N : Nat) {delta : Real} (hdelta : 0 < delta) :
    Nonempty (E.NormalBoundaryBandFamily mu (P.orbitBox N)
      ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
  classical
  obtain ⟨baseLeft, hbaseLeft⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseRight, hbaseRight⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement N 0
  obtain ⟨baseBottomSwap, hbaseBottom⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseTopSwap, hbaseTop⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_leftComplement N 0
  let baseBottom := siteAxisSwap baseBottomSwap
  let baseTop := siteAxisSwap baseTopSwap
  have hinsideLeft (margin : Nat) (i : Fin (margin + 1)) :
      P.shift (baseLeft + horizontalShift i.val) ''
          (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices 0 := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseLeft u hu
    change 0 ≤ E.vertexCoord (P.shift baseLeft u) 0 at h
    simp only [E.vertexCoord_shift] at h
    change 0 ≤ E.vertexCoord
      (P.shift (baseLeft + horizontalShift i.val) u) 0
    simp only [P.shift_add, E.vertexCoord_shift]
    simpa using add_nonneg h (show (0 : Real) ≤ i.val by positivity)
  have hinsideRight (margin : Nat) (i : Fin (margin + 1)) :
      P.shift (baseRight + horizontalShift (-(i.val : Int))) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 0 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseRight u hu
    change ¬ (0 ≤ E.vertexCoord (P.shift baseRight u) 0) at h
    simp only [E.vertexCoord_shift] at h
    change E.vertexCoord
      (P.shift (baseRight + horizontalShift (-(i.val : Int))) u) 0 ≤ 0
    simp only [P.shift_add, E.vertexCoord_shift]
    have hi : (0 : Real) ≤ i.val := by positivity
    simp only [horizontalShift_zero_apply, Int.cast_neg, Int.cast_natCast]
    linarith
  have hinsideBottom (margin : Nat) (i : Fin (margin + 1)) :
      P.shift (baseBottom + verticalShift i.val) ''
          (P.orbitBox N : Set V) ⊆ {u | 0 ≤ E.vertexCoord u 1} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseBottom u (by rw [P.axisSwap_orbitBox]; exact hu)
    change 0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseBottomSwap u) 0 at h
    have h' : 0 ≤ E.vertexCoord (P.shift baseBottom u) 1 := by
      simpa [baseBottom, PeriodicGraph.axisSwap] using h
    simp only [E.vertexCoord_shift] at h'
    change 0 ≤ E.vertexCoord
      (P.shift (baseBottom + verticalShift i.val) u) 1
    simp only [P.shift_add, E.vertexCoord_shift]
    simpa using add_nonneg h' (show (0 : Real) ≤ i.val by positivity)
  have hinsideTop (margin : Nat) (i : Fin (margin + 1)) :
      P.shift (baseTop + verticalShift (-(i.val : Int))) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 1 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseTop u (by rw [P.axisSwap_orbitBox]; exact hu)
    change ¬ (0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseTopSwap u) 0) at h
    have h' : ¬ (0 ≤ E.vertexCoord (P.shift baseTop u) 1) := by
      simpa [baseTop, PeriodicGraph.axisSwap] using h
    simp only [E.vertexCoord_shift] at h'
    change E.vertexCoord
      (P.shift (baseTop + verticalShift (-(i.val : Int))) u) 1 ≤ 0
    simp only [P.shift_add, E.vertexCoord_shift]
    have hi : (0 : Real) ≤ i.val := by positivity
    simp only [verticalShift_one_apply, Int.cast_neg, Int.cast_natCast]
    linarith
  choose radiusLeft hleft using fun margin ↦
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) ↦ baseLeft + horizontalShift i.val)
      (hinsideLeft margin) hdelta
  choose radiusRight hright using fun margin ↦
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) ↦
        baseRight + horizontalShift (-(i.val : Int)))
      (by simpa only [neg_zero] using hinsideRight margin) hdelta
  choose radiusBottom hbottom using fun margin ↦
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) ↦ baseBottom + verticalShift i.val)
      (hinsideBottom margin) hdelta
  choose radiusTop htop using fun margin ↦
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) ↦
        baseTop + verticalShift (-(i.val : Int)))
      (by simpa only [neg_zero] using hinsideTop margin) hdelta
  exact ⟨{
    baseLeft := baseLeft
    baseRight := baseRight
    baseBottom := baseBottom
    baseTop := baseTop
    radiusLeft := radiusLeft
    radiusRight := radiusRight
    radiusBottom := radiusBottom
    radiusTop := radiusTop
    left := by
      intro margin
      simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
        PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent] using hleft margin
    right := by
      intro margin
      simpa using hright margin
    bottom := by
      intro margin
      simpa using hbottom margin
    top := by
      intro margin
      simpa using htop margin }⟩


end StatMech.FK.PeriodicPlanar
