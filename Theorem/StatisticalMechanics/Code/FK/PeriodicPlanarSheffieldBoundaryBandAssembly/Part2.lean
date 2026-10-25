/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.exists_orbitBox_boundaryBandSeed
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (N width height : Nat) {delta : Real} (hdelta : 0 < delta) :
    Nonempty (E.BoundaryBandSeed mu (P.orbitBox N) width height
      ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
  classical
  obtain ⟨baseLeft, hbaseLeft⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseRight, hbaseRight⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement N (-(width : Real))
  obtain ⟨baseBottomSwap, hbaseBottom⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseTopSwap, hbaseTop⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_leftComplement N (-(height : Real))
  let baseBottom := siteAxisSwap baseBottomSwap
  let baseTop := siteAxisSwap baseTopSwap
  have hinsideLeft (v : PreferenceGridVertex width height) :
      P.shift (baseLeft + preferenceGridSite v) ''
          (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices 0 := by
    rintro _ ⟨u, hu, rfl⟩
    have huLeft := hbaseLeft u hu
    change 0 ≤ E.vertexCoord (P.shift baseLeft u) 0 at huLeft
    simp only [E.vertexCoord_shift] at huLeft
    change 0 ≤ E.vertexCoord
      (P.shift (baseLeft + preferenceGridSite v) u) 0
    simp only [P.shift_add, E.vertexCoord_shift, preferenceGridSite]
    norm_num
    exact add_nonneg huLeft (by positivity)
  have hinsideRight (v : PreferenceGridVertex width height) :
      P.shift (baseRight + preferenceGridSite v) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 0 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have huRight := hbaseRight u hu
    change ¬ (-(width : Real) ≤
      E.vertexCoord (P.shift baseRight u) 0) at huRight
    change E.vertexCoord
      (P.shift (baseRight + preferenceGridSite v) u) 0 ≤ 0
    have hv : (v.1.val : Real) ≤ width := by
      exact_mod_cast Nat.le_of_lt_succ v.1.isLt
    simp only [E.vertexCoord_shift] at huRight
    simp only [P.shift_add, E.vertexCoord_shift, preferenceGridSite]
    norm_num
    linarith
  have hinsideBottom (v : PreferenceGridVertex width height) :
      P.shift (baseBottom + preferenceGridSite v) ''
          (P.orbitBox N : Set V) ⊆ {u | 0 ≤ E.vertexCoord u 1} := by
    rintro _ ⟨u, hu, rfl⟩
    have huBottom := hbaseBottom u (by
      rw [P.axisSwap_orbitBox]
      exact hu)
    change 0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseBottomSwap u) 0 at huBottom
    have huBottom' : 0 ≤ E.vertexCoord (P.shift baseBottom u) 1 := by
      simpa [baseBottom, PeriodicGraph.axisSwap] using huBottom
    simp only [E.vertexCoord_shift] at huBottom'
    change 0 ≤ E.vertexCoord
      (P.shift (baseBottom + preferenceGridSite v) u) 1
    simp only [P.shift_add, E.vertexCoord_shift, preferenceGridSite]
    norm_num
    exact add_nonneg huBottom' (by positivity)
  have hinsideTop (v : PreferenceGridVertex width height) :
      P.shift (baseTop + preferenceGridSite v) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 1 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have huTop := hbaseTop u (by
      rw [P.axisSwap_orbitBox]
      exact hu)
    change ¬ (-(height : Real) ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseTopSwap u) 0) at huTop
    have huTop' : ¬ (-(height : Real) ≤
        E.vertexCoord (P.shift baseTop u) 1) := by
      simpa [baseTop, PeriodicGraph.axisSwap] using huTop
    change E.vertexCoord
      (P.shift (baseTop + preferenceGridSite v) u) 1 ≤ 0
    have hv : (v.2.val : Real) ≤ height := by
      exact_mod_cast Nat.le_of_lt_succ v.2.isLt
    simp only [E.vertexCoord_shift] at huTop'
    simp only [P.shift_add, E.vertexCoord_shift, preferenceGridSite]
    norm_num
    linarith
  obtain ⟨radiusLeft, hleft⟩ :=
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun v : PreferenceGridVertex width height =>
        baseLeft + preferenceGridSite v) hinsideLeft hdelta
  obtain ⟨radiusRight, hright⟩ :=
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun v : PreferenceGridVertex width height =>
        baseRight + preferenceGridSite v)
      (by simpa only [neg_zero] using hinsideRight) hdelta
  obtain ⟨radiusBottom, hbottom⟩ :=
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun v : PreferenceGridVertex width height =>
        baseBottom + preferenceGridSite v) hinsideBottom hdelta
  obtain ⟨radiusTop, htop⟩ :=
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun v : PreferenceGridVertex width height =>
        baseTop + preferenceGridSite v)
      (by simpa only [neg_zero] using hinsideTop) hdelta
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
      simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
        PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent] using hleft
    right := by simpa using hright
    bottom := by simpa using hbottom
    top := by simpa using htop }⟩


end StatMech.FK.PeriodicPlanar
