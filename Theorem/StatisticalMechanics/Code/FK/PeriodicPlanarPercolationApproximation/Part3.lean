/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarParameterMonotonicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V]

theorem PeriodicGraph.bufferedRootBoundaryEvent_isIncreasing
    (P : PeriodicGraph V) (n : Nat) :
    IsIncreasing (P.bufferedRootBoundaryEvent n) := by
  intro omega eta home hmem
  obtain ⟨v, hv, hreach⟩ := hmem
  refine ⟨v, hv, hreach.mono ?_⟩
  intro x y hxy
  rw [FK.openSub_adj] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  apply Bool.eq_true_of_true_le
  simpa [hxy.2] using home s(x, y)

theorem PeriodicGraph.openSub_bufferedRestrict_eq_induce
    (P : PeriodicGraph V) (n : Nat) (omega : ConfigSpace (Sym2 V)) :
    FK.openSub (P.bufferedGraph n) (P.bufferedRestrict n omega) =
      (P.openSubgraph omega).induce
        (P.orbitBox (P.bufferedRadius n) : Set V) := by
  ext x y
  simp only [FK.openSub_adj, SimpleGraph.induce_adj,
    PeriodicGraph.openSubgraph_adj]
  rfl

theorem PeriodicGraph.bufferedReachable_iff_inducedReachable
    (P : PeriodicGraph V) (n : Nat) (omega : ConfigSpace (Sym2 V))
    (x y : P.BufferedVertex n) :
    (FK.openSub (P.bufferedGraph n) (P.bufferedRestrict n omega)).Reachable x y ↔
      ((P.openSubgraph omega).induce
        (P.orbitBox (P.bufferedRadius n) : Set V)).Reachable x y := by
  rw [P.openSub_bufferedRestrict_eq_induce]

theorem PeriodicGraph.bufferedReachable_full
    (P : PeriodicGraph V) (n : Nat) (omega : ConfigSpace (Sym2 V))
    {x y : P.BufferedVertex n}
    (h : (FK.openSub (P.bufferedGraph n)
      (P.bufferedRestrict n omega)).Reachable x y) :
    (P.openSubgraph omega).Reachable x.1 y.1 := by
  rw [P.bufferedReachable_iff_inducedReachable] at h
  exact h.map (SimpleGraph.Embedding.induce _).toHom


theorem PeriodicGraph.bufferedBoundary_reachable_of_reachable_outside
    (P : PeriodicGraph V) (n : Nat) (omega : ConfigSpace (Sym2 V))
    {x z : V} (hx : x ∈ P.orbitBox (P.bufferedRadius n))
    (hz : z ∉ P.orbitBox (P.bufferedRadius n))
    (hreach : (P.openSubgraph omega).Reachable x z) :
    ∃ y : P.BufferedVertex n, P.bufferedBoundary n y ∧
      (FK.openSub (P.bufferedGraph n)
        (P.bufferedRestrict n omega)).Reachable ⟨x, hx⟩ y := by
  obtain ⟨y, hyreach, w, hyw, hw⟩ :=
    reachable_induce_innerBoundary (P.openSubgraph omega)
      (P.orbitBox (P.bufferedRadius n) : Set V) hx hz hreach
  refine ⟨y, ⟨w, hyw.1, hw⟩, ?_⟩
  rw [P.bufferedReachable_iff_inducedReachable]
  exact hyreach


theorem PeriodicGraph.bufferedBoundary_not_mem_of_lt
    (P : PeriodicGraph V) {n m : Nat} (hnm : n < m)
    (v : P.BufferedVertex m) (hv : P.bufferedBoundary m v) :
    v.1 ∉ P.orbitBox (P.bufferedRadius n) := by
  intro hvn
  obtain ⟨w, hvw, hw⟩ := hv
  have hwSucc := P.neighbor_mem_buffered_succ n hvn hvw
  have hnm' : n + 1 ≤ m := hnm
  exact hw (P.orbitBox_mono
    (P.bufferedRadius_strictMono.monotone hnm') hwSucc)


theorem PeriodicGraph.bufferedRootBoundaryCylinder_antitone
    (P : PeriodicGraph V) :
    Antitone (fun n => P.bufferedCylinder n
      (P.bufferedRootBoundaryEvent n)) := by
  intro n m hnm omega homega
  rcases hnm.eq_or_lt with rfl | hlt
  · exact homega
  · obtain ⟨v, hvbd, hvreach⟩ := homega
    have hfull : (P.openSubgraph omega).Reachable P.root v.1 := by
      simpa only [P.bufferedRoot_val] using
        P.bufferedReachable_full m omega hvreach
    obtain ⟨y, hybd, hyreach⟩ :=
      P.bufferedBoundary_reachable_of_reachable_outside n omega
        (P.bufferedRoot n).2 (P.bufferedBoundary_not_mem_of_lt hlt v hvbd)
        hfull
    exact ⟨y, hybd, hyreach⟩


theorem PeriodicGraph.iInter_bufferedRootBoundaryCylinder
    (P : PeriodicGraph V) :
    (⋂ n : Nat, P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)) =
      P.percolationEvent := by
  classical
  ext omega
  simp only [Set.mem_iInter, PeriodicGraph.bufferedCylinder,
    Set.mem_preimage, PeriodicGraph.bufferedRootBoundaryEvent,
    PeriodicGraph.percolationEvent, Set.mem_setOf_eq]
  constructor
  · intro hall
    by_contra hfinite
    have hcluster : (P.cluster omega P.root).Finite := Set.not_infinite.mp hfinite
    obtain ⟨n, hn⟩ := P.finite_subset_orbitBox hcluster.toFinset
    obtain ⟨v, hvbd, hvreach⟩ := hall (n + 1)
    have hfull : (P.openSubgraph omega).Reachable P.root v.1 := by
      simpa only [P.bufferedRoot_val] using
        P.bufferedReachable_full (n + 1) omega hvreach
    have hvCluster : v.1 ∈ P.cluster omega P.root := hfull
    have hvn : v.1 ∈ P.orbitBox n := by
      apply hn v.1
      simpa using hvCluster
    have hvBuffered : v.1 ∈ P.orbitBox (P.bufferedRadius n) :=
      P.orbitBox_mono (P.id_le_bufferedRadius n) hvn
    exact (P.not_bufferedBoundary_incl_succ n
      ⟨v.1, hvBuffered⟩) (by simpa using hvbd)
  · intro hinf n
    have hnotSubset : ¬P.cluster omega P.root ⊆
        (P.orbitBox (P.bufferedRadius n) : Set V) := by
      intro hsub
      exact hinf (Set.Finite.subset (P.orbitBox (P.bufferedRadius n)).finite_toSet hsub)
    obtain ⟨z, hzreach, hzout⟩ := Set.not_subset.mp hnotSubset
    obtain ⟨y, hybd, hyreach⟩ :=
      P.bufferedBoundary_reachable_of_reachable_outside n omega
        (P.bufferedRoot n).2 hzout hzreach
    exact ⟨y, hybd, hyreach⟩

section Countable

variable [Countable V]


theorem PeriodicGraph.bufferedRootBoundaryCylinder_real_tendsto_measure
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu] :
    Tendsto
      (fun n => mu.real
        (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)))
      atTop (nhds (mu.real P.percolationEvent)) := by
  have htend := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun n => (P.bufferedCylinder_measurableSet n
      (P.bufferedRootBoundaryEvent n)).nullMeasurableSet)
    P.bufferedRootBoundaryCylinder_antitone
    ⟨0, measure_ne_top mu _⟩
  rw [P.iInter_bufferedRootBoundaryCylinder] at htend
  have hreal :=
    (ENNReal.tendsto_toReal (measure_ne_top mu P.percolationEvent)).comp htend
  simpa only [Function.comp_apply, Measure.real] using hreal


theorem PeriodicGraph.bufferedRootBoundaryCylinder_real_tendsto
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Tendsto
      (fun n =>
        (P.wiredBufferedInfiniteVolume hp hp1 hq :
          Measure (ConfigSpace (Sym2 V))).real
          (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)))
      atTop (nhds (P.wiredPercolationProbability p q)) := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.wiredBufferedInfiniteVolume hp hp1 hq
  have htend := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun n => (P.bufferedCylinder_measurableSet n
      (P.bufferedRootBoundaryEvent n)).nullMeasurableSet)
    P.bufferedRootBoundaryCylinder_antitone
    ⟨0, measure_ne_top mu _⟩
  rw [P.iInter_bufferedRootBoundaryCylinder] at htend
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top mu P.percolationEvent)).comp htend
  rw [PeriodicGraph.wiredPercolationProbability, dif_pos ⟨⟨hp, hp1⟩, hq⟩]
  simpa only [Function.comp_apply, Measure.real] using hreal


theorem PeriodicGraph.hasPercolationCylinderApproximation
    (P : PeriodicGraph V) {q : Real} (hq : 1 ≤ q) :
    P.HasPercolationCylinderApproximation q := by
  refine ⟨P.bufferedRootBoundaryEvent,
    P.bufferedRootBoundaryEvent_isIncreasing, ?_⟩
  intro p hp hp1 _
  exact P.bufferedRootBoundaryCylinder_real_tendsto hp hp1
    (zero_lt_one.trans_le hq)


theorem PeriodicGraph.wiredPercolationProbability_monotoneOn
    (P : PeriodicGraph V) {q : Real} (hq : 1 ≤ q) :
    MonotoneOn (fun p => P.wiredPercolationProbability p q)
      (Ioo (0 : Real) 1) :=
  P.wiredPercolationProbability_monotoneOn_of_cylinderApproximation hq
    (P.hasPercolationCylinderApproximation hq)


theorem PeriodicGraph.offCriticalSharpness
    (P : PeriodicGraph V) {q : Real} (hq : 1 ≤ q)
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1) :
    OffCriticalSharpness
      (fun p => P.wiredPercolates p q) (P.criticalPoint q) :=
  P.offCriticalSharpness_of_monotoneOn hpc
    (P.wiredPercolationProbability_monotoneOn hq)


theorem PeriodicGraph.dualCritical_relation_of_noCoexistence
    {W : Type*} [DecidableEq W] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 1 ≤ q)
    (hcoverage : DualSubcriticalCoverage
      (fun p => Pdual.wiredPercolates p q) (P.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q) :
    BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  exact P.dualCritical_relation_of_cylinderApproximation_noCoexistence Pdual
    hpc hpcDual hq (P.hasPercolationCylinderApproximation hq)
      (Pdual.hasPercolationCylinderApproximation hq) hcoverage hnoCoexistence

end Countable
end StatMech.FK.PeriodicPlanar
