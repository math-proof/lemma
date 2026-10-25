/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncationLimit.Part2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredComparison
open Filter MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation

noncomputable section

theorem measurableSet_wiredTruncationErrorEvent
    (d R : Nat) (x : Site d) :
    MeasurableSet (wiredTruncationErrorEvent d R x) := by
  apply MeasurableSet.diff
  · exact (measurableSet_clusterInfiniteEvent x).preimage
      (continuous_wiredTruncationEdge d R).measurable
  · exact measurableSet_clusterInfiniteEvent x


theorem tendsto_wiredTruncationErrorEvent_real_zero
    {d : Nat} (x : Site d)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    Tendsto (fun R => (edgeMeasure : Measure _).real
        (wiredTruncationErrorEvent d R x)) atTop (nhds 0) := by
  let F : Nat -> ConfigSpace (Sym2 (Site d)) -> Real := fun R omega =>
    (wiredTruncationErrorEvent d R x).indicator (fun _ => 1) omega
  have hmeas : ∀ R, Measurable (F R) := by
    intro R
    exact measurable_const.indicator
      (measurableSet_wiredTruncationErrorEvent d R x)
  have hpoint : ∀ omega, Tendsto (fun R => F R omega) atTop (nhds 0) := by
    intro omega
    rcases (cluster d omega x).finite_or_infinite with hfinite | hinfinite
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_cluster_wiredTruncationEdge_eq_of_finite
        omega x hfinite] with R hR
      simp [F, wiredTruncationErrorEvent, wiredTruncatedInfiniteEvent,
        clusterInfiniteEvent, hR, hfinite]
    · apply tendsto_const_nhds.congr'
      filter_upwards with R
      simp [F, wiredTruncationErrorEvent, clusterInfiniteEvent, hinfinite]
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (edgeMeasure : Measure _))
    (F := F) (f := fun _ => (0 : Real))
    (fun _ => (1 : Real))
    (fun R => (hmeas R).aestronglyMeasurable)
    (integrable_const 1)
    (by
      intro R
      filter_upwards with omega
      by_cases h : omega ∈ wiredTruncationErrorEvent d R x
      · simp [F, Set.indicator_of_mem h]
      · simp [F, Set.indicator_of_notMem h])
    (Filter.Eventually.of_forall hpoint)
  have hdct' : Tendsto (fun R => ∫ omega, F R omega
      ∂(edgeMeasure : Measure _)) atTop (nhds 0) := by
    simpa using hdct
  apply hdct'.congr'
  filter_upwards with R
  rw [integral_indicator_const (1 : Real)
    (measurableSet_wiredTruncationErrorEvent d R x)]
  simp [F]


theorem tendsto_wiredTruncationErrorEvent_real_of_tendsto
    {d R : Nat} {I : Type*} {L : Filter I}
    (hd : 2 ≤ d) (hR : 1 ≤ R) (x : Site d) (hx : x ∈ box d R)
    (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hedge : Tendsto edgeSeq L (nhds edgeLimit))
    (hinfinite : Tendsto (fun i => (edgeSeq i : Measure _).real
        (clusterInfiniteEvent d x)) L
      (nhds ((edgeLimit : Measure _).real (clusterInfiniteEvent d x)))) :
    Tendsto (fun i => (edgeSeq i : Measure _).real
        (wiredTruncationErrorEvent d R x)) L
      (nhds ((edgeLimit : Measure _).real
        (wiredTruncationErrorEvent d R x))) := by
  have hsub : clusterInfiniteEvent d x ⊆ wiredTruncatedInfiniteEvent d R x := by
    intro omega hinfiniteOmega
    exact cluster_wiredTruncationEdge_infinite_of_infinite
      hd hR omega x hx hinfiniteOmega
  have htruncated : Tendsto (fun i => (edgeSeq i : Measure _).real
      (wiredTruncatedInfiniteEvent d R x)) L
      (nhds ((edgeLimit : Measure _).real
        (wiredTruncatedInfiniteEvent d R x))) := by
    have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
      hedge (isClopen_wiredTruncatedInfiniteEvent hd hR x hx)
    simpa [Measure.real] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hNN
  have hdiffSeq (i : I) :
      (edgeSeq i : Measure _).real (wiredTruncationErrorEvent d R x) =
        (edgeSeq i : Measure _).real (wiredTruncatedInfiniteEvent d R x) -
          (edgeSeq i : Measure _).real (clusterInfiniteEvent d x) := by
    exact measureReal_diff hsub (measurableSet_clusterInfiniteEvent x)
  have hdiffLimit :
      (edgeLimit : Measure _).real (wiredTruncationErrorEvent d R x) =
        (edgeLimit : Measure _).real (wiredTruncatedInfiniteEvent d R x) -
          (edgeLimit : Measure _).real (clusterInfiniteEvent d x) := by
    exact measureReal_diff hsub (measurableSet_clusterInfiniteEvent x)
  have ht := htruncated.sub hinfinite
  rw [← hdiffLimit] at ht
  exact ht.congr' (Filter.Eventually.of_forall fun i => (hdiffSeq i).symm)


end
end StatMech.FK
