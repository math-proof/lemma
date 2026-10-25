/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentAfterMixing
import Theorem.StatisticalMechanics.Code.FrontierB.PlusAxisMixing
import Theorem.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCoarseUniqueness
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPersistence
import Theorem.StatisticalMechanics.Code.FK.PairMixingGenMixing
import Def.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceMixing
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


theorem infinitePlusCurrentTraceLaw_axisEventuallyGenMixing
    {d : Nat} (hd : 1 <= d) {beta : Real} (hbeta : 0 < beta) :
    fmu_AxisEventuallyGenMixing
      (fun k => FK.freeAxisTranslationPower hd k)
      (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  intro family hfamily epsilon hepsilon
  rw [Filter.eventually_all_finset family]
  intro A hA
  rw [Filter.eventually_all_finset family]
  intro B hB
  have hAmeas : MeasurableSet A :=
    MeasurableSet.of_mem_measurableCylinders (hfamily A hA)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.of_mem_measurableCylinders (hfamily B hB)
  let PA := currentTrace ⁻¹' A
  let PB := currentTrace ⁻¹' B
  have hPA : PA ∈ measurableCylinders
      (fun _ : Sym2 (Site d) => Nat) :=
    currentTrace_preimage_mem_measurableCylinders (hfamily A hA)
  have hPB : PB ∈ measurableCylinders
      (fun _ : Sym2 (Site d) => Nat) :=
    currentTrace_preimage_mem_measurableCylinders (hfamily B hB)
  let nu := (infinitePlusCurrentMeasure d beta hbeta.le :
    Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  have ht := infinitePlusCurrentMeasure_cylinder_axis_pairCorrelation_tendsto
    hd hbeta PA PB hPA hPB
  have hev := ht.eventually (Metric.ball_mem_nhds
    (nu.real PA * nu.real PB) hepsilon)
  filter_upwards [hev] with k hk
  have hABmeas : MeasurableSet (A ∩
      (shift (FK.freeAxisTranslationPower hd k)) ⁻¹' B) :=
    hAmeas.inter (hBmeas.preimage
      (measurable_shift (FK.freeAxisTranslationPower hd k)))
  rw [currentTraceLaw_real _ hABmeas,
    currentTraceLaw_real _ hAmeas, currentTraceLaw_real _ hBmeas,
    currentTrace_preimage_inter_shift]
  simpa only [PA, PB, Real.dist_eq] using (Metric.mem_ball.mp hk)


theorem infiniteFreeCurrentTraceLaw_axisCofinalGenMixing
    {d : Nat} (hd : 1 <= d) {beta : Real} (hbeta : 0 < beta) :
    fmu_AxisCofinalGenMixing
      (fun k => FK.freeAxisTranslationPower hd k)
      (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  intro family hfamily epsilon hepsilon K
  let pulled : Finset
      (Set (InfiniteCurrentConfig (Sym2 (Site d)))) :=
    family.image (fun A => currentTrace ⁻¹' A)
  have hpulled : ∀ A ∈ pulled,
      A ∈ measurableCylinders (fun _ : Sym2 (Site d) => Nat) := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨C, hC, rfl⟩ := hA
    exact currentTrace_preimage_mem_measurableCylinders (hfamily C hC)
  obtain ⟨k, hk, hmix⟩ :=
    infiniteFreeCurrentMeasure_cylinderPairMixing_after
      hd hbeta K pulled hpulled epsilon hepsilon
  refine ⟨k, hk, ?_⟩
  intro A hA B hB
  have hAmeas : MeasurableSet A :=
    MeasurableSet.of_mem_measurableCylinders (hfamily A hA)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.of_mem_measurableCylinders (hfamily B hB)
  have hABmeas : MeasurableSet (A ∩
      (shift (FK.freeAxisTranslationPower hd k)) ⁻¹' B) :=
    hAmeas.inter (hBmeas.preimage
      (measurable_shift (FK.freeAxisTranslationPower hd k)))
  rw [currentTraceLaw_real _ hABmeas,
    currentTraceLaw_real _ hAmeas, currentTraceLaw_real _ hBmeas,
    currentTrace_preimage_inter_shift]
  exact hmix (currentTrace ⁻¹' A)
    (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
    (currentTrace ⁻¹' B)
    (Finset.mem_image.mpr ⟨B, hB, rfl⟩)


end StatMech.FrontierB
