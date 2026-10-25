/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.bufferedTwoPointCylinder_subset_twoPointEvent
    (P : PeriodicGraph V) (N : ℕ) (x y : P.BufferedVertex N) :
    P.bufferedCylinder N (P.bufferedTwoPointEvent N x y) ⊆
      P.twoPointEvent x.1 y.1 := by
  intro omega homega
  exact P.bufferedReachable_full N omega homega


theorem PeriodicGraph.freeBufferedInfiniteVolume_le_wired_cylinder
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  have hfree := P.freeBufferedMeasure_tendsto_cylinder N hp hp1 hq hS
  have hwired := P.wiredBufferedMeasure_tendsto_cylinder N hp hp1 hq hS
  have heventually : ∀ᶠ m in atTop,
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤
        (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
    filter_upwards [eventually_ge_atTop N] with m hm
    rw [P.freeBufferedMeasure_real_cylinder hm hp hp1 (zero_lt_one.trans_le hq),
      P.wiredBufferedMeasure_real_cylinder hm hp hp1 (zero_lt_one.trans_le hq)]
    have hpre : IsIncreasing (P.bufferedRestrictLE hm ⁻¹' S) :=
      fun omega eta home hmem =>
        hS (P.monotone_bufferedRestrictLE hm home) hmem
    exact fkProb_le_wiredFkProb_increasing
      (G := P.bufferedGraph m) (bdry := P.bufferedBoundary m)
      hp hp1 hq hpre
  exact le_of_tendsto_of_tendsto hfree hwired heventually


theorem PeriodicGraph.freeBufferedTwoPointCylinder_le_wiredTwoPoint
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x y : P.BufferedVertex N) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V)))
        (P.bufferedCylinder N (P.bufferedTwoPointEvent N x y)) ≤
      ENNReal.ofReal (P.wiredTwoPointProbability p q x.1 y.1) := by
  let muf : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  let muw : Measure (ConfigSpace (Sym2 V)) :=
    P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have hreal : muf.real
        (P.bufferedCylinder N (P.bufferedTwoPointEvent N x y)) ≤
      muw.real (P.twoPointEvent x.1 y.1) :=
    (P.freeBufferedInfiniteVolume_le_wired_cylinder N hp hp1 hq
      (P.bufferedTwoPointEvent_isIncreasing N x y)).trans
      (measureReal_mono
        (P.bufferedTwoPointCylinder_subset_twoPointEvent N x y))
  have hrange : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q :=
    ⟨⟨hp, hp1⟩, zero_lt_one.trans_le hq⟩
  rw [PeriodicGraph.wiredTwoPointProbability, dif_pos hrange]
  rw [← ENNReal.ofReal_toReal (measure_ne_top muf _)]
  exact ENNReal.ofReal_le_ofReal hreal


theorem PeriodicGraph.measurableSet_cluster_infinite
    (P : PeriodicGraph V) (x : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      (P.cluster omega x).Infinite} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite} =
      ⋂ n : ℕ, ⋃ y : {y : V // y ∉ P.orbitBox n},
        P.twoPointEvent x y.1 := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      PeriodicGraph.twoPointEvent, PeriodicGraph.cluster]
    constructor
    · intro hinf n
      by_contra hnone
      push Not at hnone
      have hsub : P.cluster omega x ⊆ (P.orbitBox n : Set V) := by
        intro y hy
        by_contra hyout
        exact hnone ⟨y, hyout⟩ hy
      exact hinf ((P.orbitBox n).finite_toSet.subset hsub)
    · intro hout hfinite
      obtain ⟨n, hn⟩ := P.finite_subset_orbitBox hfinite.toFinset
      obtain ⟨y, hy⟩ := hout n
      exact y.2 (hn y.1 (by simpa using hy))
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun y =>
    P.measurableSet_twoPointEvent x y.1


theorem PeriodicGraph.measurableSet_hasInfiniteCluster
    (P : PeriodicGraph V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteCluster omega} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteCluster omega} =
      ⋃ x : V, {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite} := by
    ext omega
    simp [PeriodicGraph.HasInfiniteCluster]
  rw [heq]
  exact MeasurableSet.iUnion fun x => P.measurableSet_cluster_infinite x

end StatMech.FK.PeriodicPlanar
