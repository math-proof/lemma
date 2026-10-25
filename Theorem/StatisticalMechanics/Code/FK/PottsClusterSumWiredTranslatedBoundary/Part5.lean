/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part5
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

theorem centeredMarkedBoundaryMass_eq_of_mem
    {d n : Nat} {x : Site d} (hx : x ∈ box d n) (p q : Real) :
    centeredMarkedBoundaryMass d x n p q =
      wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q ⟨x, hx⟩ := by
  simp [centeredMarkedBoundaryMass, boxMarkedVertex_eq_of_mem hx]


theorem centered_origin_wiredConnToBdryMass_eq_measure
    {d n : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q
        (boxOrigin d n) =
      (wiredFiniteMeasure d n hp hp1 hq : Measure _).real
        (boxBdryConnEvent d n) := by
  have h := fkgq_wiredFiniteMeasure_real_boxRestrictEvent
    (d := d) n hp hp1 hq
    (finiteConnToBdryEvent (boxGraph d n) (boxBoundary d n) (boxOrigin d n))
    (measurableSet_boxBdryConnEvent d n)
  simpa [wiredConnToBdryMass, finiteConnToBdryEvent,
    boxBdryConnEvent] using h.symm


theorem centered_origin_wiredConnToBdryMass_tendsto
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n => wiredConnToBdryMass
        (boxGraph d n) (boxBoundary d n) p q (boxOrigin d n))
      atTop (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
  have h := fkgq_boxBdryConnEvent_diag_tendsto (d := d) hp hp1 hq
  exact h.congr' (Filter.Eventually.of_forall fun n =>
    (centered_origin_wiredConnToBdryMass_eq_measure
      (d := d) (n := n) hp hp1 (zero_lt_one.trans_le hq)).symm)


theorem centeredMarkedBoundaryMass_tendsto
    {d : Nat} (x : Site d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n => centeredMarkedBoundaryMass d x n p q) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
  let c := flc_vrad x
  let originMass := fun n => wiredConnToBdryMass
    (boxGraph d n) (boxBoundary d n) p q (boxOrigin d n)
  have horigin : Tendsto originMass atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
    simpa only [originMass] using
      centered_origin_wiredConnToBdryMass_tendsto hp hp1 hq
  have hlo : Tendsto (fun n => originMass (n + c + 1)) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
    exact horigin.comp (by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun n hn => by omega⟩)
  have hhi : Tendsto (fun n => originMass (n - c - 1)) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq))) := by
    exact horigin.comp (by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨b + c + 1, fun n hn => by omega⟩)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (max 1 c)] with n hn
    have hn1 : 1 ≤ n := le_max_left 1 c |>.trans hn
    have hcn : c ≤ n := le_max_right 1 c |>.trans hn
    have hx : x ∈ box d n := fun i => (flc_vrad_le x i).trans hcn
    rw [centeredMarkedBoundaryMass_eq_of_mem hx]
    rw [show originMass (n + c + 1) =
        wiredConnToBdryMass
          (fvs_transBoxGraph d (n + flc_vrad x + 1) x)
          (fvs_transBoxBoundary d (n + flc_vrad x + 1) x) p q
          (transBoxCenter d (n + flc_vrad x + 1) x) by
      rw [translated_wiredConnToBdryMass_eq_centered]]
    exact translated_outer_boundaryMass_le_centered_marked
      x n hn1 hcn hp hp1 hq
  · filter_upwards [eventually_ge_atTop (c + 2)] with n hn
    let k := n - c - 1
    have hk1 : 1 ≤ k := by omega
    have hkn : k + c + 1 = n := by omega
    have hx : x ∈ box d n := fun i =>
      (flc_vrad_le x i).trans (by omega)
    rw [show originMass (n - c - 1) =
        wiredConnToBdryMass (fvs_transBoxGraph d k x)
          (fvs_transBoxBoundary d k x) p q (transBoxCenter d k x) by
      rw [translated_wiredConnToBdryMass_eq_centered]]
    have hbound := centered_marked_boundaryMass_le_translated_inner
      x k hk1 hp hp1 hq
    have hkn' : k + flc_vrad x + 1 = n := by simpa only [c] using hkn
    have hxk : x ∈ box d (k + flc_vrad x + 1) := fun i =>
      (flc_vrad_le x i).trans (by omega)
    rw [← centeredMarkedBoundaryMass_eq_of_mem hxk p q] at hbound
    rw [hkn'] at hbound
    exact hbound


theorem shift_preimage_clusterInfiniteEvent_wired
    {d : Nat} (g : Multiplicative (Site d)) (x : Site d) :
    (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) -> _) ⁻¹'
        clusterInfiniteEvent d (g • x) =
      clusterInfiniteEvent d x := by
  ext omega
  change (cluster d (ConfigSpace.shift g omega) (g • x)).Infinite ↔
    (cluster d omega x).Infinite
  rw [cluster_shift]
  exact Set.infinite_image_iff
    (Set.injOn_of_injective (smul_injective g))


theorem wiredInfiniteVolume_clusterInfiniteEvent_real_eq_fkTheta
    {d : Nat} (x : Site d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (clusterInfiniteEvent d x) =
      fkTheta d hp hp1 (zero_lt_one.trans_le hq) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (-x)
  have hg : g • x = origin d := by
    change (-x) + x = origin d
    rw [neg_add_cancel]
    rfl
  have hpre :
      (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) -> _) ⁻¹'
          percolationEvent d = clusterInfiniteEvent d x := by
    have h := shift_preimage_clusterInfiniteEvent_wired (d := d) g x
    rw [hg] at h
    simpa [percolationEvent, clusterInfiniteEvent] using h
  have hpres := fkgqt_wiredIV_isTranslationInvariant hp hp1 hq g
  have hmeas : MeasurableSet (percolationEvent d) := by
    simpa [percolationEvent, clusterInfiniteEvent] using
      (measurableSet_clusterInfiniteEvent (d := d) (origin d))
  unfold fkTheta
  change mu.real (clusterInfiniteEvent d x) = mu.real (percolationEvent d)
  rw [← hpre]
  exact hpres.measureReal_preimage hmeas.nullMeasurableSet


theorem wiredOpenExterior_clusterInfiniteEvent_real_eq_centeredMarkedBoundaryMass
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n) (x : Site d)
    (hx : x ∈ box d n) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (wiredOpenExteriorFiniteMeasure d n hp hp1 hq : Measure _).real
        (clusterInfiniteEvent d x) =
      centeredMarkedBoundaryMass d x n p q := by
  let xb : boxVerts d n := ⟨x, hx⟩
  have hpre : extendWiredEdge d n ⁻¹' clusterInfiniteEvent d x =
      finiteConnToBdryEvent (boxGraph d n) (boxBoundary d n) xb := by
    ext omega
    change (cluster d (extendWiredEdge d n omega) (xb : Site d)).Infinite ↔
      ConnToBdry (boxGraph d n) (boxBoundary d n) omega xb
    exact cluster_extendWiredEdge_infinite_iff_connToBdry hd hn omega xb
  have hmeas : MeasurableSet (clusterInfiniteEvent d x) :=
    measurableSet_clusterInfiniteEvent x
  unfold wiredOpenExteriorFiniteMeasure
  change (Measure.map (extendWiredEdge d n)
      (wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
        (clusterInfiniteEvent d x)).toReal = _
  rw [Measure.map_apply (measurable_extendWiredEdge d n) hmeas,
    hpre, wiredFkPMF_toMeasure_toReal]
  rw [centeredMarkedBoundaryMass_eq_of_mem hx]
  rfl


theorem wiredOpenExterior_clusterInfiniteEvent_real_tendsto
    {d : Nat} (hd : 2 ≤ d) (x : Site d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n =>
        (wiredOpenExteriorFiniteMeasure d n hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (clusterInfiniteEvent d x)) atTop
      (nhds ((wiredInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (clusterInfiniteEvent d x))) := by
  have hmass := centeredMarkedBoundaryMass_tendsto x hp hp1 hq
  have heq : (λ n =>
      (wiredOpenExteriorFiniteMeasure d n hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (clusterInfiniteEvent d x)) =ᶠ[atTop]
      (λ n => centeredMarkedBoundaryMass d x n p q) := by
    filter_upwards [eventually_ge_atTop (max 1 (flc_vrad x))] with n hn
    have hn1 : 1 ≤ n := le_max_left 1 (flc_vrad x) |>.trans hn
    have hxn : flc_vrad x ≤ n :=
      le_max_right 1 (flc_vrad x) |>.trans hn
    have hx : x ∈ box d n := fun i => (flc_vrad_le x i).trans hxn
    exact wiredOpenExterior_clusterInfiniteEvent_real_eq_centeredMarkedBoundaryMass
      hd hn1 x hx hp hp1 (zero_lt_one.trans_le hq)
  rw [wiredInfiniteVolume_clusterInfiniteEvent_real_eq_fkTheta x hp hp1 hq]
  exact hmass.congr' heq.symm


end
end StatMech.FK
