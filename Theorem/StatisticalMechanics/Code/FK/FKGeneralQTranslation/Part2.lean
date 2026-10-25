/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
import Def.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech.FK

open StatMech.IsingFK

variable {d : ℕ}


theorem fkgqt_centred_eq_translated_free (m : ℕ) (v : Site d)
    (t : Finset (Sym2 (boxVerts d m))) (p q : ℝ) :
    med_multiMassProb (fkProb (boxGraph d m) p q) t =
      med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p q)
        (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (fkProb (boxGraph d m) p q)
    (fkProb (fvs_transBoxGraph d m v) p q)
    (fun omega ↦ fvs_fkProb_reCfgIso (boxGraph d m)
      (fvs_transBoxGraph d m v) (fvs_transEquiv d m v)
      (fvs_transEquiv_adj d m v) p q omega)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun omega _ ↦ ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]


theorem fkgqt_centred_med_eq_measure_free (n : ℕ)
    (tb : Finset (Sym2 (boxVerts d n))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    med_multiMassProb (fkProb (boxGraph d n) p q) tb =
      (freeFiniteMeasure d n hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (tb.image (edgeIncl d n))) := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict n tb]
  have hmeas : MeasurableSet
      (boxRestrict d n ⁻¹' cdc_boxMultiOpenEvent n tb) :=
    (continuous_boxRestrict d n).measurable MeasurableSet.of_discrete
  rw [freeFiniteMeasure_real_boxRestrictEvent n hp hp1 hq
    (cdc_boxMultiOpenEvent n tb) hmeas]
  rfl


theorem fkgqt_transBoxMassFree_eq_centred (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (m : ℕ) (hNm : N ≤ m) :
    fkgqt_transBoxMassFree v N t p q m hNm =
      (freeFiniteMeasure d m hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [fkgqt_transBoxMassFree]
  unfold flc_transEdges
  rw [← fkgqt_centred_eq_translated_free m v
    (t.image (innerEdgeLE d hNm)) p q]
  rw [fkgqt_centred_med_eq_measure_free m
    (t.image (innerEdgeLE d hNm)) hp hp1 hq]
  congr 2
  rw [Finset.image_image]
  exact Finset.image_congr (fun eb _ ↦ edgeIncl_innerEdgeLE d hNm eb)


theorem fkgqt_transBoxMassFree_tendsto_centred_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k : ℕ ↦ fkgqt_transBoxMassFree v N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  have hbase := fkgq_free_infinite_measure N hp hp1 hq
    (cdc_boxMultiOpenEvent_isIncreasing (d := d) N t)
  rw [← cdc_multiOpenEvent_image_eq_boxRestrict N t] at hbase
  have hshift := hbase.comp (tendsto_add_atTop_nat N)
  refine hshift.congr' ?_
  filter_upwards with k
  simpa only [Function.comp_apply, Nat.add_comm] using
    (fkgqt_transBoxMassFree_eq_centred v N t hp hp1
      (zero_lt_one.trans_le hq) (N + k) (Nat.le_add_right N k)).symm


theorem fkgqt_freeSqueeze_upper (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m : ℕ) (hNm : N ≤ m) :
    fkgqt_transBoxMassFree v N t p q m hNm ≤
      (freeFiniteMeasure d (m + flc_vrad v + 1) hp hp1
        (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
  set c := flc_vrad v with hc
  have hsub : fvs_transBox d m v ⊆ box d (m + c + 1) :=
    (flc_transBox_subset_box v m).trans (box_mono d (by omega))
  have hdom := bdp_latticeFree_multiMass_dominated
    (Sin := fvs_transBox d m v) (Sout := box d (m + c + 1))
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    hp hp1 hq (flc_transEdges v N t m hNm)
  rw [fkgqt_transBoxMassFree]
  refine hdom.trans (le_of_eq ?_)
  change med_multiMassProb (fkProb (boxGraph d (m + c + 1)) p q)
      ((flc_transEdges v N t m hNm).image
        (ocd_innerEdge (flc_incl hsub))) = _
  rw [fkgqt_centred_med_eq_measure_free (m + c + 1)
    ((flc_transEdges v N t m hNm).image
      (ocd_innerEdge (flc_incl hsub))) hp hp1
      (zero_lt_one.trans_le hq)]
  congr 2
  rw [show edgeIncl d (m + c + 1) =
      Sym2.map (Subtype.val : boxVerts d (m + c + 1) → Site d) from rfl,
    flc_valImage_ocd_innerEdge_image hsub (flc_transEdges v N t m hNm),
    flc_valImage_transEdges v N t m hNm]


theorem fkgqt_freeSqueeze_lower (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m a : ℕ) (hNm : N ≤ m)
    (hcond : a + flc_vrad v + 1 ≤ m)
    (tb : Finset (Sym2 (boxVerts d a)))
    (htb : tb.image (edgeIncl d a) =
      (t.image (edgeIncl d N)).image
        (fun e ↦ (Multiplicative.ofAdd v) • e)) :
    (freeFiniteMeasure d a hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site d)))).real
        (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
          (fun e ↦ (Multiplicative.ofAdd v) • e))) ≤
      fkgqt_transBoxMassFree v N t p q m hNm := by
  have hsub : box d a ⊆ fvs_transBox d m v :=
    flc_box_subset_transBox v (by omega : a + flc_vrad v ≤ m)
  have hdom := bdp_latticeFree_multiMass_dominated
    (Sin := box d a) (Sout := fvs_transBox d m v)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    hp hp1 hq tb
  have hkey : tb.image (ocd_innerEdge (flc_incl hsub)) =
      flc_transEdges v N t m hNm := by
    apply flc_image_eq_of_val_image_eq
    rw [flc_valImage_transEdges v N t m hNm,
      flc_valImage_ocd_innerEdge_image hsub tb,
      show Sym2.map (Subtype.val : boxVerts d a → Site d) =
        edgeIncl d a from rfl, htb]
  rw [fkgqt_transBoxMassFree, ← hkey]
  refine le_trans (le_of_eq ?_) hdom
  change _ = med_multiMassProb (fkProb (boxGraph d a) p q) tb
  rw [fkgqt_centred_med_eq_measure_free a tb hp hp1
    (zero_lt_one.trans_le hq), htb]


theorem fkgqt_transBoxMassFree_tendsto_translated_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k : ℕ ↦ fkgqt_transBoxMassFree v N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e ↦ (Multiplicative.ofAdd v) • e))))) := by
  classical
  let c := flc_vrad v
  let vs := (t.image (edgeIncl d N)).image
    (fun e ↦ (Multiplicative.ofAdd v) • e)
  obtain ⟨N', t', hvs⟩ := cdc_finset_in_box vs
  let L := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)
  have hbase : Tendsto (fun r ↦
      (freeFiniteMeasure d r hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    have h := fkgq_free_infinite_measure N' hp hp1 hq
      (cdc_boxMultiOpenEvent_isIncreasing (d := d) N' t')
    rw [← cdc_multiOpenEvent_image_eq_boxRestrict N' t', ← hvs] at h
    exact h
  have hlo : Tendsto (fun k : ℕ ↦
      (freeFiniteMeasure d ((N + k) - c - 1) hp hp1
        (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b + N + c + 1, fun k hk ↦ by omega⟩
  have hhi : Tendsto (fun k : ℕ ↦
      (freeFiniteMeasure d ((N + k) + c + 1) hp hp1
        (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun k hk ↦ by omega⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (N' + c + 2)] with k hk
    have hNa : N' ≤ (N + k) - c - 1 := by omega
    have hcond : ((N + k) - c - 1) + flc_vrad v + 1 ≤ N + k := by
      change ((N + k) - c - 1) + c + 1 ≤ N + k
      omega
    have htb : (t'.image (innerEdgeLE d hNa)).image
        (edgeIncl d ((N + k) - c - 1)) = vs := by
      rw [Finset.image_image]
      calc
        t'.image (edgeIncl d ((N + k) - c - 1) ∘ innerEdgeLE d hNa) =
            t'.image (edgeIncl d N') := by
              apply Finset.image_congr
              intro eb _
              exact edgeIncl_innerEdgeLE d hNa eb
        _ = vs := hvs.symm
    change _ ≤ fkgqt_transBoxMassFree v N t p q (N + k) _
    simpa only [vs, c] using fkgqt_freeSqueeze_lower v N t hp hp1 hq
      (N + k) ((N + k) - c - 1) (Nat.le_add_right N k) hcond
      (t'.image (innerEdgeLE d hNa)) htb
  · filter_upwards with k
    change fkgqt_transBoxMassFree v N t p q (N + k) _ ≤ _
    simpa only [vs, c] using fkgqt_freeSqueeze_upper v N t hp hp1 hq
      (N + k) (Nat.le_add_right N k)


theorem fkgqt_free_multiOpen_translation (v : Site d)
    (s : Finset (Sym2 (Site d))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
        (cdc_multiOpenEvent s) =
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
        (cdc_multiOpenEvent (s.image
          (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
  obtain ⟨N, t, hs⟩ := cdc_finset_in_box s
  have h1 := fkgqt_transBoxMassFree_tendsto_centred_iv v N t hp hp1 hq
  have h2 := fkgqt_transBoxMassFree_tendsto_translated_iv v N t hp hp1 hq
  have hreal := tendsto_nhds_unique h1 h2
  rw [← hs] at hreal
  let μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  change (μ (cdc_multiOpenEvent s)).toReal =
    (μ (cdc_multiOpenEvent (s.image
      (fun e ↦ (Multiplicative.ofAdd v) • e)))).toReal at hreal
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top μ _) (measure_ne_top μ _)).mp hreal


theorem fkgqt_freeIV_isTranslationInvariant {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  let μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsProbabilityMeasure (Measure.map (shift g) μ) :=
    inferInstance
  refine ⟨measurable_shift g, ?_⟩
  apply fkgqt_measure_eq_of_multiOpen_eq
  intro T
  rw [Measure.map_apply (measurable_shift g) (fmu_multiOpen_measurable T),
    fmu_shift_multiOpen]
  simpa only [ofAdd_toAdd] using
    (fkgqt_free_multiOpen_translation (Multiplicative.toAdd g⁻¹) T
      hp hp1 hq).symm

end StatMech.FK
