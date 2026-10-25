/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


namespace PeriodicPlanarDualPair

variable [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


@[simp] theorem swap_primalEmbedding
    (D : PeriodicPlanarDualPair P Pdual) :
    D.swap.primalEmbedding = D.dualEmbedding := rfl

@[simp] theorem swap_dualEmbedding
    (D : PeriodicPlanarDualPair P Pdual) :
    D.swap.dualEmbedding = D.primalEmbedding := rfl


theorem PeriodicPlaneEmbedding.shift_ne_of_ne
    (E : PeriodicPlaneEmbedding P) {z : Site 2} (hz : z ≠ 0) (x : V) :
    P.shift z x ≠ x := by
  intro hfix
  have hperiod : E.period z = 0 := by
    have hshift := E.vertex_shift z x
    rw [hfix] at hshift
    have hcancel : E.vertex x + E.period z = E.vertex x + 0 := by
      simpa using hshift.symm
    exact add_left_cancel hcancel
  exact hz (E.period_injective (hperiod.trans E.period.map_zero.symm))


theorem PeriodicGraph.orbitBox_card_le_quadratic
    (P : PeriodicGraph V) (n : ℕ) :
    (P.orbitBox n).card ≤ (2 * n + 1) ^ 2 * P.fundamentalDomain.card := by
  rw [PeriodicGraph.orbitBox]
  calc
    ((((box_finite 2 n).toFinset ×ˢ P.fundamentalDomain).image
      (fun zu => P.shift zu.1 zu.2))).card ≤
        ((box_finite 2 n).toFinset ×ˢ P.fundamentalDomain).card :=
      Finset.card_image_le
    _ = (2 * n + 1) ^ 2 * P.fundamentalDomain.card := by
      rw [Finset.card_product, ← boxSV_boxF_eq_toFinset, boxSV_card_boxF]


theorem probabilityMeasure_eq_of_finiteCylinder_real_eq
    {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (ConfigSpace E))
    (h : ∀ (s : Finset E) (S : Set (∀ _i : s, Bool)),
      (mu : Measure (ConfigSpace E)).real (cylinder s S) =
        (nu : Measure (ConfigSpace E)).real (cylinder s S)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨s, S, _hS, rfl⟩ := hC
    have hreal := h s S
    unfold Measure.real at hreal
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (mu : Measure (ConfigSpace E)) (cylinder s S))
      (measure_ne_top (nu : Measure (ConfigSpace E)) (cylinder s S))).mp hreal
  · rw [measure_univ, measure_univ]


theorem free_wired_infiniteVolume_dual
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Pdual.wiredBufferedInfiniteVolume
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) =
      (P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq)).map
        (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable :=
  D.free_wired_infiniteVolume_dual_law hp hp1 hq


theorem wired_free_infiniteVolume_dual
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Pdual.freeBufferedInfiniteVolume
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) =
      (P.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq)).map
        (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable :=
  D.wired_free_infiniteVolume_dual_law hp hp1 hq


theorem percolationEvent_measurableSet (P : PeriodicGraph V) :
    MeasurableSet P.percolationEvent := by
  rw [← P.iInter_bufferedRootBoundaryCylinder]
  exact MeasurableSet.iInter fun n =>
    P.bufferedCylinder_measurableSet n (P.bufferedRootBoundaryEvent n)


theorem wiredDual_percolationEvent
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ((Pdual.wiredBufferedInfiniteVolume
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 W))) :
      Measure (ConfigSpace (Sym2 W))) Pdual.percolationEvent =
    ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V)))
      ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.percolationEvent) := by
  apply weakLimit_dual_event D.edgeDual
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq))
    (Pdual.wiredBufferedInfiniteVolume
      (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
      (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
      (zero_lt_one.trans_le hq))
    (D.free_wired_infiniteVolume_dual hp hp1 hq)
    (percolationEvent_measurableSet Pdual)


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
