/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


theorem zbd_boxHitsInfinite_isIncreasing (n : ℕ) : IsIncreasing (zbd_boxHitsInfinite n) := by
  intro ω ω' hle
  rintro ⟨x, hx, hinf⟩
  exact ⟨x, hx, hinf.mono (cluster_mono hle x)⟩

theorem zbd_boxHitsInfinite_measurableSet (n : ℕ) :
    MeasurableSet (zbd_boxHitsInfinite n) := by
  have heq : zbd_boxHitsInfinite n = ⋃ x : Site 2,
      if x ∈ box 2 n then {ω | (cluster 2 ω x).Infinite} else ∅ := by
    ext ω
    simp only [zbd_boxHitsInfinite, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hinf⟩
      exact ⟨x, by simp [hx, hinf]⟩
    · rintro ⟨x, hx⟩
      by_cases hxb : x ∈ box 2 n
      · exact ⟨x, hxb, by simpa [hxb] using hx⟩
      · simp [hxb] at hx
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ box 2 n
  · simpa [hx] using (measurableSet_clusterInfinite (d := 2) x)
  · simp [hx]

theorem zbd_boxHitsInfinite_mono : Monotone zbd_boxHitsInfinite := by
  intro n m hnm ω
  rintro ⟨x, hx, hinf⟩
  refine ⟨x, ?_, hinf⟩
  rw [mem_box] at hx ⊢
  intro i
  exact le_trans (hx i) hnm


theorem zbd_iUnion_boxHitsInfinite :
    (⋃ n, zbd_boxHitsInfinite n) =
      {ω : ConfigSpace (Sym2 (Site 2)) | ∃ x : Site 2, (cluster 2 ω x).Infinite} := by
  ext ω
  simp only [Set.mem_iUnion, zbd_boxHitsInfinite, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, x, _hx, hinf⟩
    exact ⟨x, hinf⟩
  · rintro ⟨x, hinf⟩
    have hxall : x ∈ ⋃ n, box 2 n := by rw [iUnion_box]; trivial
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hxall
    exact ⟨n, x, hx, hinf⟩


theorem zbd_existsInfinite_halfMeasure_one
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    halfMeasure {ω : ConfigSpace (Sym2 (Site 2)) | ∃ x : Site 2,
      (cluster 2 ω x).Infinite} = 1 := by
  have hbk := (bins_bk_unconditional (2⁻¹ : NNReal) half_le_one
    (by norm_num) (by norm_num)).1
  rcases hbk with hzero | hone
  · have hsub : Universality.percolationEvent 2 ⊆
        {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = 0}ᶜ := by
      intro ω hω hcount
      have hmem : cluster 2 ω 0 ∈ infiniteClusters 2 ω := ⟨hω, 0, rfl⟩
      have hempty : infiniteClusters 2 ω = ∅ := by
        apply (Set.encard_eq_zero.mp ?_)
        simpa [numInfiniteClusters] using hcount
      simpa [hempty] using hmem
    have hnull : halfMeasure (Universality.percolationEvent 2) = 0 := by
      apply measure_mono_null hsub
      exact (prob_compl_eq_zero_iff (measurable_numInfiniteClusters
        (MeasurableSet.singleton 0))).2 hzero
    simp [Measure.real, hnull] at hpos
  · have hsub : {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = 1} ⊆
        {ω : ConfigSpace (Sym2 (Site 2)) | ∃ x : Site 2, (cluster 2 ω x).Infinite} := by
      intro ω hcount
      have hne : infiniteClusters 2 ω ≠ ∅ := by
        intro hempty
        have : numInfiniteClusters 2 ω = 0 := by simp [numInfiniteClusters, hempty]
        rw [hcount] at this
        norm_num at this
      obtain ⟨C, hC⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact ⟨hC.2.choose, hC.2.choose_spec ▸ hC.1⟩
    exact le_antisymm prob_le_one (hone ▸ measure_mono hsub)


theorem zbd_boxHit_rotated_union_tendsto
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto (fun n =>
      halfMeasure.real (zrs_sideFamily (zbd_boxHitsInfinite n) 0
        ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 1
        ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 2
        ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 3)) atTop (nhds 1) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := halfMeasure) zbd_boxHitsInfinite_mono
  rw [zbd_iUnion_boxHitsInfinite, zbd_existsInfinite_halfMeasure_one hpos] at hmeasure
  have hreal : Tendsto (fun n => halfMeasure.real (zbd_boxHitsInfinite n)) atTop (nhds 1) := by
    exact (ENNReal.tendsto_toReal (by norm_num : (1 : ENNReal) ≠ ∞)).comp hmeasure
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hreal tendsto_const_nhds
  · intro n
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    exact Or.inl (Or.inl (Or.inl hω))
  · intro n
    exact measureReal_le_one


theorem zbd_connectedWithin_box_of_connected {d : ℕ}
    (omega : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hxy : Connected d omega x y) :
    ∃ n, ∃ (hx : x ∈ box d n) (hy : y ∈ box d n),
      ConnectedWithin d omega (box d n) ⟨x, hx⟩ ⟨y, hy⟩ := by
  rcases hxy with ⟨w⟩
  obtain ⟨n, hn⟩ := StatMech.Percolation.finite_subset_box
    ({z : Site d | z ∈ w.support}) w.support.finite_toSet
  have hx : x ∈ box d n := hn w.start_mem_support
  have hy : y ∈ box d n := hn w.end_mem_support
  exact ⟨n, hx, hy, ⟨w.induce (box d n) hn⟩⟩


end StatMech.TwoDim
