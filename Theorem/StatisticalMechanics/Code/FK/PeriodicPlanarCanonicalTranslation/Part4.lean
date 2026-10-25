/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part6
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

theorem PeriodicGraph.bufferedEdgeLift_image
    (P : PeriodicGraph V) (N : Nat) (T : Finset (Sym2 V))
    (hT : ∀ e ∈ T, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
    (P.bufferedEdgeLift N T hT).image
        (P.edgeIncl (P.bufferedRadius N)) = T := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨eb, heb, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨e', he'T, heq⟩ := Finset.mem_image.1 heb
    rw [← heq, (hT e'.1 e'.2).choose_spec]
    exact e'.2
  · intro he
    apply Finset.mem_image.2
    refine ⟨(hT e he).choose, ?_, (hT e he).choose_spec⟩
    apply Finset.mem_image.2
    exact ⟨⟨e, he⟩, Finset.mem_attach _ _, rfl⟩

theorem PeriodicGraph.shiftedFreeMultiMass_tendsto_centered
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k => P.shiftedFreeMultiMass z N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius N)))))) := by
  have hbase := (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (isClopen_fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius N))))
  have hsub := hbase.comp (tendsto_add_atTop_nat N)
  refine hsub.congr' ?_
  filter_upwards with k
  symm
  simpa only [Function.comp_apply, Nat.add_comm] using
    P.shiftedFreeMultiMass_eq_centered z N t hp hp1 hq
      (N + k) (Nat.le_add_right N k)

theorem PeriodicGraph.shiftedFreeMultiMass_tendsto_shifted
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k => P.shiftedFreeMultiMass z N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image
            (Sym2.map (P.shift z)))))) := by
  classical
  let T := (t.image (P.edgeIncl (P.bufferedRadius N))).image
    (Sym2.map (P.shift z))
  obtain ⟨N', hN'⟩ := P.exists_bufferedLevel_edges T
  let t' := P.bufferedEdgeLift N' T hN'
  have ht' : t'.image (P.edgeIncl (P.bufferedRadius N')) = T :=
    P.bufferedEdgeLift_image N' T hN'
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have hbase : Tendsto (fun r =>
      (P.freeBufferedMeasure r hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (fmu_multiOpen T)) atTop
      (nhds (mu.real (fmu_multiOpen T))) :=
    (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
      (isClopen_fmu_multiOpen T)
  let c := flc_vrad z
  have hlo : Tendsto (fun k =>
      (P.freeBufferedMeasure ((N + k) - c) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (fmu_multiOpen T)) atTop (nhds (mu.real (fmu_multiOpen T))) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b + N + c, fun k hk => by omega⟩
  have hhi : Tendsto (fun k =>
      (P.freeBufferedMeasure ((N + k) + c) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (fmu_multiOpen T)) atTop (nhds (mu.real (fmu_multiOpen T))) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun k hk => by omega⟩
  change Tendsto _ _ (nhds (mu.real (fmu_multiOpen T)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (N' + c)] with k hk
    let a := (N + k) - c
    have hN'a : N' ≤ a := by dsimp only [a, c]; omega
    let ta := t'.image (Sym2.map (P.bufferedVertexInclLE hN'a))
    have hta : ta.image (P.edgeIncl (P.bufferedRadius a)) = T := by
      dsimp only [ta]
      rw [Finset.image_image]
      calc
        t'.image (P.edgeIncl (P.bufferedRadius a) ∘
            Sym2.map (P.bufferedVertexInclLE hN'a)) =
            t'.image (P.edgeIncl (P.bufferedRadius N')) := by
              apply Finset.image_congr
              intro e he
              exact P.edgeIncl_bufferedVertexInclLE hN'a e
        _ = T := ht'
    have ha : a + flc_vrad z ≤ N + k := by dsimp only [a, c]; omega
    change _ ≤ P.shiftedFreeMultiMass z N t p q (N + k) _
    simpa only [T, c] using P.centered_shift_le_shiftedFreeMultiMass
      z N t hp hp1 hq (N + k) a (Nat.le_add_right N k) ha ta hta
  · filter_upwards with k
    change P.shiftedFreeMultiMass z N t p q (N + k) _ ≤ _
    simpa only [T, c] using P.shiftedFreeMultiMass_le_centered_shift
      z N t hp hp1 hq (N + k) (Nat.le_add_right N k)


theorem PeriodicGraph.freeBufferedInfiniteVolume_multiOpen_shift
    (P : PeriodicGraph V) (z : Site 2) (T : Finset (Sym2 V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V))) (fmu_multiOpen T) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V)))
        (fmu_multiOpen (T.image (Sym2.map (P.shift z)))) := by
  obtain ⟨N, hN⟩ := P.exists_bufferedLevel_edges T
  let t := P.bufferedEdgeLift N T hN
  have ht : t.image (P.edgeIncl (P.bufferedRadius N)) = T :=
    P.bufferedEdgeLift_image N T hN
  have hcenter := P.shiftedFreeMultiMass_tendsto_centered z N t hp hp1 hq
  have hshift := P.shiftedFreeMultiMass_tendsto_shifted z N t hp hp1 hq
  have hreal := tendsto_nhds_unique hcenter hshift
  rw [ht] at hreal
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

theorem PeriodicGraph.configTranslate_preimage_fmu_multiOpen
    (P : PeriodicGraph V) (z : Site 2) (T : Finset (Sym2 V)) :
    P.configTranslate z ⁻¹' fmu_multiOpen T =
      fmu_multiOpen (T.image (Sym2.map (P.shift (-z)))) := by
  ext omega
  simp only [Set.mem_preimage, fmu_multiOpen, Set.mem_setOf_eq,
    PeriodicGraph.configTranslate, Finset.forall_mem_image]


theorem PeriodicGraph.freeBufferedInfiniteVolume_isTranslationInvariant
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    P.IsTranslationInvariant
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))) := by
  intro z
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  haveI : IsProbabilityMeasure mu := by
    dsimp only [mu]
    infer_instance
  haveI : IsProbabilityMeasure (Measure.map (P.configTranslate z) mu) :=
    inferInstance
  refine MeasurePreserving.mk (P.measurable_configTranslate z) ?_
  apply fkgqt_measure_eq_of_multiOpen_eq
  intro T
  rw [Measure.map_apply (P.measurable_configTranslate z)
    (fmu_multiOpen_measurable T),
    P.configTranslate_preimage_fmu_multiOpen z T]
  exact (P.freeBufferedInfiniteVolume_multiOpen_shift (-z) T hp hp1 hq).symm

end StatMech.FK.PeriodicPlanar
