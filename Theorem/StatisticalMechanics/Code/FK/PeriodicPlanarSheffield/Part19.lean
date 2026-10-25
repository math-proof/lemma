/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part19
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.hasUniqueInfiniteCluster_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.HasUniqueInfiniteCluster (P.configTranslate z omega) ↔
      P.HasUniqueInfiniteCluster omega := by
  constructor
  · rintro ⟨⟨x, hx⟩, huniq⟩
    refine ⟨⟨P.shift (-z) x, ?_⟩, ?_⟩
    · exact (P.cluster_infinite_configTranslate z omega
        (P.shift (-z) x)).mp (by simpa using hx)
    · intro a b ha hb
      have ha' : (P.cluster (P.configTranslate z omega)
          (P.shift z a)).Infinite :=
        (P.cluster_infinite_configTranslate z omega a).2 ha
      have hb' : (P.cluster (P.configTranslate z omega)
          (P.shift z b)).Infinite :=
        (P.cluster_infinite_configTranslate z omega b).2 hb
      exact (P.reachable_configTranslate z omega a b).mp
        (huniq (P.shift z a) (P.shift z b) ha' hb')
  · rintro ⟨⟨x, hx⟩, huniq⟩
    refine ⟨⟨P.shift z x,
      (P.cluster_infinite_configTranslate z omega x).2 hx⟩, ?_⟩
    intro a b ha hb
    let a0 := P.shift (-z) a
    let b0 := P.shift (-z) b
    have ha0 : (P.cluster omega a0).Infinite :=
      (P.cluster_infinite_configTranslate z omega a0).mp
        (by simpa [a0] using ha)
    have hb0 : (P.cluster omega b0).Infinite :=
      (P.cluster_infinite_configTranslate z omega b0).mp
        (by simpa [b0] using hb)
    have hab := huniq a0 b0 ha0 hb0
    simpa [a0, b0] using
      (P.reachable_configTranslate z omega a0 b0).mpr hab

theorem PeriodicGraph.clusterInfinite_isIncreasing
    (P : PeriodicGraph V) (x : V) :
    IsIncreasing {omega : ConfigSpace (Sym2 V) |
      (P.cluster omega x).Infinite} := by
  intro omega eta home hinfinite
  have hgraph : P.openSubgraph omega ≤ P.openSubgraph eta := by
    intro a b hab
    rw [P.openSubgraph_adj] at hab ⊢
    refine ⟨hab.1, Bool.eq_true_of_true_le ?_⟩
    simpa [hab.2] using home s(a, b)
  exact hinfinite.mono fun y hy => hy.mono hgraph

theorem PeriodicGraph.orbitBoxHitsInfinite_measurableSet
    (P : PeriodicGraph V) (n : ℕ) :
    MeasurableSet (P.orbitBoxHitsInfinite n) := by
  have heq : P.orbitBoxHitsInfinite n =
      ⋃ x : V, if x ∈ P.orbitBox n then
        {omega : ConfigSpace (Sym2 V) |
          (P.cluster omega x).Infinite} else ∅ := by
    ext omega
    simp only [PeriodicGraph.orbitBoxHitsInfinite, Set.mem_setOf_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hinf⟩
      exact ⟨x, by simp [hx, hinf]⟩
    · rintro ⟨x, hx⟩
      by_cases hxb : x ∈ P.orbitBox n
      · exact ⟨x, hxb, by simpa [hxb] using hx⟩
      · simp [hxb] at hx
  rw [heq]
  exact MeasurableSet.iUnion fun x => by
    by_cases hx : x ∈ P.orbitBox n
    · simpa [hx] using P.measurableSet_cluster_infinite x
    · simp [hx]

theorem PeriodicGraph.orbitBoxHitsInfinite_isIncreasing
    (P : PeriodicGraph V) (n : ℕ) :
    IsIncreasing (P.orbitBoxHitsInfinite n) := by
  intro omega eta home
  rintro ⟨x, hx, hinfinite⟩
  exact ⟨x, hx, P.clusterInfinite_isIncreasing x home hinfinite⟩

theorem PeriodicGraph.translatedOrbitBoxHitsInfinite_preimage
    (P : PeriodicGraph V) (z : Site 2) (n : ℕ) :
    P.configTranslate z ⁻¹' P.translatedOrbitBoxHitsInfinite z n =
      P.orbitBoxHitsInfinite n := by
  ext omega
  simp only [Set.mem_preimage, PeriodicGraph.translatedOrbitBoxHitsInfinite,
    PeriodicGraph.orbitBoxHitsInfinite, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hinf⟩
    exact ⟨x, hx, (P.cluster_infinite_configTranslate z omega x).mp hinf⟩
  · rintro ⟨x, hx, hinf⟩
    exact ⟨x, hx, (P.cluster_infinite_configTranslate z omega x).mpr hinf⟩

theorem PeriodicGraph.translatedOrbitBoxHitsInfinite_measurableSet
    (P : PeriodicGraph V) (z : Site 2) (n : ℕ) :
    MeasurableSet (P.translatedOrbitBoxHitsInfinite z n) := by
  have heq : P.translatedOrbitBoxHitsInfinite z n =
      ⋃ x : V, if x ∈ P.orbitBox n then
        {omega : ConfigSpace (Sym2 V) |
          (P.cluster omega (P.shift z x)).Infinite} else ∅ := by
    ext omega
    simp only [PeriodicGraph.translatedOrbitBoxHitsInfinite,
      Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hinf⟩
      exact ⟨x, by simp [hx, hinf]⟩
    · rintro ⟨x, hx⟩
      by_cases hxb : x ∈ P.orbitBox n
      · exact ⟨x, hxb, by simpa [hxb] using hx⟩
      · simp [hxb] at hx
  rw [heq]
  exact MeasurableSet.iUnion fun x => by
    by_cases hx : x ∈ P.orbitBox n
    · simpa [hx] using P.measurableSet_cluster_infinite (P.shift z x)
    · simp [hx]

theorem PeriodicGraph.translatedOrbitBoxHitsInfinite_measure_eq
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (n : ℕ) :
    mu (P.translatedOrbitBoxHitsInfinite z n) =
      mu (P.orbitBoxHitsInfinite n) := by
  rw [← P.translatedOrbitBoxHitsInfinite_preimage z n]
  exact ((hTI z).measure_preimage
    (P.translatedOrbitBoxHitsInfinite_measurableSet z n).nullMeasurableSet).symm

theorem PeriodicGraph.orbitBoxHitsInfinite_mono
    (P : PeriodicGraph V) : Monotone P.orbitBoxHitsInfinite := by
  intro n m hnm omega
  rintro ⟨x, hx, hinf⟩
  exact ⟨x, P.orbitBox_mono hnm hx, hinf⟩

theorem PeriodicGraph.iUnion_orbitBoxHitsInfinite
    (P : PeriodicGraph V) :
    (⋃ n, P.orbitBoxHitsInfinite n) =
      {omega | P.HasInfiniteCluster omega} := by
  ext omega
  simp only [Set.mem_iUnion, PeriodicGraph.orbitBoxHitsInfinite,
    PeriodicGraph.HasInfiniteCluster, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, x, _hx, hinf⟩
    exact ⟨x, hinf⟩
  · rintro ⟨x, hinf⟩
    obtain ⟨n, hx⟩ := P.mem_orbitBox_of_eventually x
    exact ⟨n, x, hx, hinf⟩

theorem PeriodicGraph.orbitBoxHitsInfinite_real_tendsto_one
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
    Tendsto (fun n => mu.real (P.orbitBoxHitsInfinite n))
      atTop (nhds 1) := by
  have hmeasure := tendsto_measure_iUnion_atTop
    (μ := mu) P.orbitBoxHitsInfinite_mono
  rw [P.iUnion_orbitBoxHitsInfinite, hexists] at hmeasure
  exact (ENNReal.tendsto_toReal (by norm_num : (1 : ENNReal) ≠ ⊤)).comp
    hmeasure

theorem PeriodicGraph.measurableSet_hasUniqueInfiniteCluster
    (P : PeriodicGraph V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.HasUniqueInfiniteCluster omega} := by
  let Inf := fun x : V =>
    {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite}
  let Conn := fun x y : V => P.twoPointEvent x y
  have heq : {omega : ConfigSpace (Sym2 V) |
        P.HasUniqueInfiniteCluster omega} =
      {omega | P.HasInfiniteCluster omega} ∩
        ⋂ x : V, ⋂ y : V, ((Inf x ∩ Inf y) ∩ (Conn x y)ᶜ)ᶜ := by
    ext omega
    simp only [PeriodicGraph.HasUniqueInfiniteCluster, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      not_and, Inf, Conn, PeriodicGraph.twoPointEvent]
    aesop
  rw [heq]
  apply P.measurableSet_hasInfiniteCluster.inter
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
    (((P.measurableSet_cluster_infinite x).inter
      (P.measurableSet_cluster_infinite y)).inter
      (P.measurableSet_twoPointEvent x y).compl).compl


end StatMech.FK.PeriodicPlanar
