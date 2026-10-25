/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneErgodic
import Def.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}


theorem twoArmDisconnectedTraceEvent_tail_antitone
    {R : ℕ} {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R) :
    Antitone (fun n => twoArmDisconnectedTraceEvent (R + n + 1) x y) := by
  intro m n hmn
  apply twoArmDisconnectedTraceEvent_antitone_of_mem (by omega)
  · simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R m) hx
  · simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R m) hy
  · omega


theorem iInter_twoArmDisconnectedTraceEvent
    {R : ℕ} {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R) :
    (⋂ n, twoArmDisconnectedTraceEvent (R + n + 1) x y) =
      distinctInfiniteClusterEvent x y := by
  ext ω
  simp only [Set.mem_iInter, distinctInfiniteClusterEvent, Set.mem_setOf_eq]
  constructor
  · intro h
    have hnotconn : ¬ Connected d ω x y := by
      intro hconn
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp
        ((mem_iUnion_boxConnectionEvent_iff_connected ω x y).2 hconn)
      have hlarge := boxConnectionEvent_mono x y (by omega : m ≤ R + m + 1) hm
      exact (mem_twoArmDisconnectedTraceEvent.1 (h m)).2.2 hlarge
    have hxinf : (cluster d ω x).Infinite := by
      rw [cluster_infinite_iff]
      intro m
      obtain ⟨_, z, _, hzBoundary, hxz⟩ :=
        (mem_twoArmDisconnectedTraceEvent.1 (h m)).1
      refine ⟨z, ?_, hxz.connected⟩
      intro hzm
      exact hzBoundary.2 (box_mono d (by omega) hzm)
    have hyinf : (cluster d ω y).Infinite := by
      rw [cluster_infinite_iff]
      intro m
      obtain ⟨_, z, _, hzBoundary, hyz⟩ :=
        (mem_twoArmDisconnectedTraceEvent.1 (h m)).2.1
      refine ⟨z, ?_, hyz.connected⟩
      intro hzm
      exact hzBoundary.2 (box_mono d (by omega) hzm)
    exact ⟨hxinf, hyinf, hnotconn⟩
  · rintro ⟨hxinf, hyinf, hnotconn⟩ n
    have hxr : x ∈ box d (R + n + 1 - 1) := by
      simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R n) hx
    have hyr : y ∈ box d (R + n + 1 - 1) := by
      simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R n) hy
    obtain ⟨zx, hzxout, hxzx⟩ :=
      (cluster_infinite_iff ω x).1 hxinf (R + n + 1 - 1)
    obtain ⟨zy, hzyout, hyzy⟩ :=
      (cluster_infinite_iff ω y).1 hyinf (R + n + 1 - 1)
    rw [mem_twoArmDisconnectedTraceEvent]
    refine ⟨mem_traceBoundaryConnectionEvent.1
        (mem_traceBoundaryConnectionEvent_of_connected_outside (by omega) hxr hzxout hxzx),
      mem_traceBoundaryConnectionEvent.1
        (mem_traceBoundaryConnectionEvent_of_connected_outside (by omega) hyr hzyout hyzy), ?_⟩
    intro hbox
    exact hnotconn hbox.2.2.connected


theorem distinctInfiniteClusterEvent_subset_atLeastTwoInfinite (x y : Site d) :
    distinctInfiniteClusterEvent x y ⊆ atLeastTwoInfinite d := by
  intro ω hω
  obtain ⟨hxinf, hyinf, hxy⟩ := hω
  have hne : cluster d ω x ≠ cluster d ω y := by
    intro heq
    apply hxy
    rw [← mem_cluster, heq]
    exact self_mem_cluster ω y
  have hpair : ({cluster d ω x, cluster d ω y} : Set (Set (Site d))) ⊆
      infiniteClusters d ω := by
    intro C hC
    rcases hC with (rfl | hC)
    · exact ⟨hxinf, x, rfl⟩
    · have : C = cluster d ω y := by simpa using hC
      subst C
      exact ⟨hyinf, y, rfl⟩
  change 2 ≤ numInfiniteClusters d ω
  unfold numInfiniteClusters
  rw [← Set.encard_pair hne]
  exact Set.encard_le_encard hpair

theorem cnx_probabilityMeasure_coe_apply_eq_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (A : Set Ω) :
    ((μ A : NNReal) : ℝ) = (μ : Measure Ω).real A := by
  rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact (ENNReal.coe_toReal _).symm

theorem cnx_independentSuperposedTraceLaw_real
    (μ ν : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    {A : Set (ConfigSpace (Sym2 (Site d)))} (hA : MeasurableSet A) :
    (independentSuperposedTraceLaw μ ν : Measure _).real A =
      (μ.prod ν : Measure _).real (superposedCurrentTrace ⁻¹' A) := by
  rw [← cnx_probabilityMeasure_coe_apply_eq_real
      (independentSuperposedTraceLaw μ ν) A,
    ← cnx_probabilityMeasure_coe_apply_eq_real (μ.prod ν)
      (superposedCurrentTrace ⁻¹' A)]
  exact congrArg (fun z : NNReal => (z : ℝ))
    (ProbabilityMeasure.map_apply (μ.prod ν)
      continuous_superposedCurrentTrace.measurable.aemeasurable hA)


theorem WeakCurrentConverges.pairTraceClopen_real
    {μ ν : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {μLim νLim : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    (hμ : WeakCurrentConverges μ μLim)
    (hν : WeakCurrentConverges ν νLim)
    {A : Set (ConfigSpace (Sym2 (Site d)))} (hA : IsClopen A) :
    Tendsto
      (fun k => ((μ k).prod (ν k) : Measure _).real
        (superposedCurrentTrace ⁻¹' A)) atTop
      (nhds ((μLim.prod νLim : Measure _).real
        (superposedCurrentTrace ⁻¹' A))) := by
  have htrace := independentSuperposedTraceLaw_tendsto hμ hν
  have hport : Tendsto
      (fun k => (independentSuperposedTraceLaw (μ k) (ν k) : Measure _).real A)
        atTop
      (nhds ((independentSuperposedTraceLaw μLim νLim : Measure _).real A)) :=
    (show WeakConvergesTo
      (fun k => independentSuperposedTraceLaw (μ k) (ν k))
      (independentSuperposedTraceLaw μLim νLim) from htrace).tendsto_real_of_isClopen hA
  have hAmeas : MeasurableSet A := hA.isOpen.measurableSet
  simpa only [cnx_independentSuperposedTraceLaw_real (d := d) (hA := hAmeas)] using hport


theorem currentPairConnectivityNoEscape_of_uniqueInfiniteCluster
    {μ ν : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {μLim νLim : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    (hμ : WeakCurrentConverges μ μLim)
    (hν : WeakCurrentConverges ν νLim)
    (hunique : (independentSuperposedTraceLaw μLim νLim : Measure _)
      (atLeastTwoInfinite d) = 0)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    CurrentPairConnectivityNoEscape μ ν Q x y := by
  obtain ⟨R, hR⟩ := Percolation.finite_subset_box
    ({x, y} : Set (Site d)) (Set.toFinite _)
  have hxR : x ∈ box d R := hR (by simp)
  have hyR : y ∈ box d R := hR (by simp)
  let traceLim := independentSuperposedTraceLaw μLim νLim
  have htail : Antitone (fun n => twoArmDisconnectedTraceEvent (R + n + 1) x y) :=
    twoArmDisconnectedTraceEvent_tail_antitone hxR hyR
  have hmeas : ∀ n, NullMeasurableSet
      (twoArmDisconnectedTraceEvent (R + n + 1) x y) (traceLim : Measure _) :=
    fun n =>
      (isClopen_twoArmDisconnectedTraceEvent
        (R + n + 1) x y).isOpen.measurableSet.nullMeasurableSet
  have hdistinctZero : (traceLim : Measure _) (distinctInfiniteClusterEvent x y) = 0 := by
    apply le_antisymm
    · calc
        (traceLim : Measure _) (distinctInfiniteClusterEvent x y) ≤
            (traceLim : Measure _) (atLeastTwoInfinite d) :=
          measure_mono (distinctInfiniteClusterEvent_subset_atLeastTwoInfinite x y)
        _ = 0 := hunique
    · exact bot_le
  have htailMeasure : Tendsto
      (fun n => (traceLim : Measure _) (twoArmDisconnectedTraceEvent (R + n + 1) x y))
      atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop (μ := (traceLim : Measure _)) hmeas htail
      ⟨0, measure_ne_top (traceLim : Measure _)
        (twoArmDisconnectedTraceEvent (R + 0 + 1) x y)⟩
    rw [iInter_twoArmDisconnectedTraceEvent hxR hyR, hdistinctZero] at h
    exact h
  have htailReal : Tendsto
      (fun n => (traceLim : Measure _).real
        (twoArmDisconnectedTraceEvent (R + n + 1) x y)) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp htailMeasure
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htailReal) δ hδ
  let M := R + N + 1
  have hlimitSmall : (traceLim : Measure _).real
      (twoArmDisconnectedTraceEvent M x y) < δ := by
    have hclose := hN N (le_refl N)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hclose
    simpa only [M] using hclose
  refine ⟨M, ?_⟩
  intro m hmM
  have hMpos : 1 ≤ M := by dsimp [M]; omega
  have hxM : x ∈ box d (M - 1) := by
    dsimp [M]
    simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R N) hxR
  have hyM : y ∈ box d (M - 1) := by
    dsimp [M]
    simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R N) hyR
  have htwoMono : twoArmDisconnectedTraceEvent m x y ⊆
      twoArmDisconnectedTraceEvent M x y :=
    twoArmDisconnectedTraceEvent_antitone_of_mem hMpos hxM hyM hmM
  have hport := hμ.pairTraceClopen_real hν
    (isClopen_twoArmDisconnectedTraceEvent M x y)
  have hMMeas : MeasurableSet (twoArmDisconnectedTraceEvent M x y) :=
    (isClopen_twoArmDisconnectedTraceEvent M x y).isOpen.measurableSet
  have hlimitPair : (μLim.prod νLim : Measure _).real
      (superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent M x y) < ε := by
    rw [← cnx_independentSuperposedTraceLaw_real μLim νLim hMMeas]
    change (traceLim : Measure _).real (twoArmDisconnectedTraceEvent M x y) < ε
    exact hlimitSmall.trans (by dsimp [δ]; linarith)
  have heventuallySmall : ∀ᶠ k in atTop,
      (((μ k).prod (ν k) : Measure _).real
        (superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent M x y)) < ε :=
    (tendsto_order.1 hport).2 ε hlimitPair
  filter_upwards [heventuallySmall, eventually_ge_atTop m] with k hkSmall hmk
  have hescape := currentPairTraceBoxGate_diff_subset_twoArm
    (Q := Q) (m := m) (k := k) (x := x) (y := y)
    (hMpos.trans hmM) (box_mono d (by omega) hxM)
      (box_mono d (by omega) hyM) hmk
  have hsubset : currentPairTraceBoxGate Q k x y \
        currentPairTraceBoxGate Q m x y ⊆
      superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent M x y :=
    hescape.trans (Set.preimage_mono htwoMono)
  exact (measureReal_mono hsubset (by finiteness)).trans_lt hkSmall

end StatMech.FrontierB
