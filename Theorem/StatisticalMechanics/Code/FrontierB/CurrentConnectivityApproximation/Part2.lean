/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteLocalSwitching.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Def.StatisticalMechanics.Code.FrontierB.CurrentConnectivityApproximation.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}


theorem isClopen_currentPairBoxConnectionEvent (n : ℕ) (x y : Site d) :
    IsClopen (currentPairBoxConnectionEvent n x y) :=
  (isClopen_boxConnectionEvent n x y).preimage continuous_superposedCurrentTrace

theorem currentPairBoxConnectionEvent_mono (x y : Site d) :
    Monotone (fun n => currentPairBoxConnectionEvent n x y) := by
  intro m n hmn p hp
  exact boxConnectionEvent_mono x y hmn hp


theorem iUnion_currentPairBoxConnectionEvent (x y : Site d) :
    (⋃ n, currentPairBoxConnectionEvent n x y) =
      currentPairConnectionEvent x y := by
  ext p
  simp only [Set.mem_iUnion, currentPairConnectionEvent,
    currentPairBoxConnectionEvent, Set.mem_preimage]
  simpa only [Set.mem_iUnion, Set.mem_setOf_eq] using
    (mem_iUnion_boxConnectionEvent_iff_connected
      (superposedCurrentTrace p) x y)

theorem probabilityMeasure_coe_apply_eq_real
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : ProbabilityMeasure Omega) (A : Set Omega) :
    ((mu A : NNReal) : ℝ) = (mu : Measure Omega).real A := by
  rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact (ENNReal.coe_toReal _).symm

theorem independentSuperposedTraceLaw_real
    (mu nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    {A : Set (ConfigSpace (Sym2 (Site d)))} (hA : MeasurableSet A) :
    (independentSuperposedTraceLaw mu nu : Measure _).real A =
      (mu.prod nu : Measure _).real (superposedCurrentTrace ⁻¹' A) := by
  rw [← probabilityMeasure_coe_apply_eq_real
      (independentSuperposedTraceLaw mu nu) A,
    ← probabilityMeasure_coe_apply_eq_real (mu.prod nu)
      (superposedCurrentTrace ⁻¹' A)]
  exact congrArg (fun z : NNReal => (z : ℝ))
    (ProbabilityMeasure.map_apply (mu.prod nu)
      continuous_superposedCurrentTrace.measurable.aemeasurable hA)


theorem WeakCurrentConverges.pairBoxConnectionEvent_real
    {mu nu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {muLim nuLim : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim)
    (m : ℕ) (x y : Site d) :
    Tendsto
      (fun k => ((mu k).prod (nu k) : Measure _).real
        (currentPairBoxConnectionEvent m x y)) atTop
      (nhds ((muLim.prod nuLim : Measure _).real
        (currentPairBoxConnectionEvent m x y))) := by
  have htrace := independentSuperposedTraceLaw_tendsto hmu hnu
  have hport : Tendsto
      (fun k => (independentSuperposedTraceLaw (mu k) (nu k) : Measure _).real
        (boxConnectionEvent m x y)) atTop
      (nhds ((independentSuperposedTraceLaw muLim nuLim : Measure _).real
        (boxConnectionEvent m x y))) :=
    (show WeakConvergesTo
      (fun k => independentSuperposedTraceLaw (mu k) (nu k))
      (independentSuperposedTraceLaw muLim nuLim) from htrace).tendsto_real_of_isClopen
        (isClopen_boxConnectionEvent m x y)
  have hA : MeasurableSet (boxConnectionEvent m x y) :=
    (isClopen_boxConnectionEvent m x y).isOpen.measurableSet
  simpa only [independentSuperposedTraceLaw_real (d := d) (hA := hA),
    currentPairBoxConnectionEvent] using hport


theorem WeakCurrentConverges.pairBoxConnectionEvent_inter_trace_real
    {mu nu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {muLim nuLim : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim)
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (m : ℕ) (x y : Site d) :
    Tendsto
      (fun k => ((mu k).prod (nu k) : Measure _).real
        (superposedCurrentTrace ⁻¹' (Q ∩ boxConnectionEvent m x y))) atTop
      (nhds ((muLim.prod nuLim : Measure _).real
        (superposedCurrentTrace ⁻¹' (Q ∩ boxConnectionEvent m x y)))) := by
  have htrace := independentSuperposedTraceLaw_tendsto hmu hnu
  have hport : Tendsto
      (fun k => (independentSuperposedTraceLaw (mu k) (nu k) : Measure _).real
        (Q ∩ boxConnectionEvent m x y)) atTop
      (nhds ((independentSuperposedTraceLaw muLim nuLim : Measure _).real
        (Q ∩ boxConnectionEvent m x y))) :=
    (show WeakConvergesTo
      (fun k => independentSuperposedTraceLaw (mu k) (nu k))
      (independentSuperposedTraceLaw muLim nuLim) from htrace).tendsto_real_of_isClopen
        (hQ.inter (isClopen_boxConnectionEvent m x y))
  have hA : MeasurableSet (Q ∩ boxConnectionEvent m x y) :=
    (hQ.inter (isClopen_boxConnectionEvent m x y)).isOpen.measurableSet
  simpa only [independentSuperposedTraceLaw_real (d := d) (hA := hA)] using hport


theorem currentPairBoxConnectionEvent_measure_tendsto
    (mu nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))) (x y : Site d) :
    Tendsto (fun n => (mu.prod nu : Measure _)
      (currentPairBoxConnectionEvent n x y)) atTop
      (nhds ((mu.prod nu : Measure _) (currentPairConnectionEvent x y))) := by
  rw [← iUnion_currentPairBoxConnectionEvent x y]
  exact
    tendsto_measure_iUnion_atTop
      (μ := (mu.prod nu : Measure _))
      (currentPairBoxConnectionEvent_mono x y)


theorem currentPairBoxConnectionEvent_inter_measure_tendsto
    (mu nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (Q : Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d)))) (x y : Site d) :
    Tendsto
      (fun n => (mu.prod nu : Measure _)
        (Q ∩ currentPairBoxConnectionEvent n x y)) atTop
      (nhds ((mu.prod nu : Measure _)
        (Q ∩ currentPairConnectionEvent x y))) := by
  have hmono : Monotone
      (fun n => Q ∩ currentPairBoxConnectionEvent n x y) :=
    monotone_const.inter (currentPairBoxConnectionEvent_mono x y)
  have hunion : (⋃ n, Q ∩ currentPairBoxConnectionEvent n x y) =
      Q ∩ currentPairConnectionEvent x y := by
    rw [← inter_iUnion, iUnion_currentPairBoxConnectionEvent]
  rw [← hunion]
  exact tendsto_measure_iUnion_atTop (μ := (mu.prod nu : Measure _)) hmono


theorem currentPairBoxConnectionEvent_inter_real_tendsto
    (mu nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (Q : Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d)))) (x y : Site d) :
    Tendsto
      (fun n => (mu.prod nu : Measure _).real
        (Q ∩ currentPairBoxConnectionEvent n x y)) atTop
      (nhds ((mu.prod nu : Measure _).real
        (Q ∩ currentPairConnectionEvent x y))) := by
  exact (ENNReal.tendsto_toReal (measure_ne_top (mu.prod nu : Measure _)
    (Q ∩ currentPairConnectionEvent x y))).comp
      (currentPairBoxConnectionEvent_inter_measure_tendsto mu nu Q x y)

end StatMech.FrontierB
