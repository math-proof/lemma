/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity.Part2
import Def.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part2
open MeasureTheory Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem spinProdBCF_apply (d : ℕ) (A : Finset (Site d))
    (omega : ConfigSpace (Site d)) :
    spinProdBCF d A omega = spinProd A omega := rfl


theorem integral_freeMeasure_spinProd_tendsto_freeState
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (A : Finset (Site d)) :
    Tendsto
      (fun n => ∫ omega, spinProd A omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  let a : ℕ → ℝ := fun n =>
    ∫ omega, spinProd A omega
      ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  have hA_add (k : ℕ) : ↑A ⊆ box d (k + N) :=
    hAN.trans (box_mono d (Nat.le_add_left N k))
  have htail_mono : Monotone (fun k => a (k + N)) := by
    intro k l hkl
    change a (k + N) ≤ a (l + N)
    rw [show a (k + N) = isingExpectation (sctBoxGraph d (k + N)) beta 0
        (spinProd (boxSpinSupport d (k + N) A)) by
      exact integral_freeMeasure_spinProd d (k + N) beta 0 A (hA_add k)]
    rw [show a (l + N) = isingExpectation (sctBoxGraph d (l + N)) beta 0
        (spinProd (boxSpinSupport d (l + N) A)) by
      exact integral_freeMeasure_spinProd d (l + N) beta 0 A (hA_add l)]
    exact isingExpectation_boxSpinSupport_mono d (Nat.add_le_add_right hkl N)
      beta hbeta A (hA_add k)
  have htail_bdd : BddAbove (Set.range (fun k => a (k + N))) := by
    refine ⟨1, ?_⟩
    rintro y ⟨k, rfl⟩
    change a (k + N) ≤ 1
    rw [show a (k + N) = isingExpectation (sctBoxGraph d (k + N)) beta 0
        (spinProd (boxSpinSupport d (k + N) A)) by
      exact integral_freeMeasure_spinProd d (k + N) beta 0 A (hA_add k)]
    exact isingExpectation_spinProd_le_one (sctBoxGraph d (k + N)) beta 0 _
  let L : ℝ := ⨆ k, a (k + N)
  have htail : Tendsto (fun k => a (k + N)) atTop (nhds L) := by
    simpa only [L] using tendsto_atTop_ciSup htail_mono htail_bdd
  have hfull : Tendsto a atTop (nhds L) :=
    (tendsto_add_atTop_iff_nat N).1 htail
  obtain ⟨phi, hphi, hweak⟩ := freeState_isInfiniteVolumeState d beta 0
  have hsub_free := hweak.tendsto_integral (spinProdBCF d A)
  have hsub_L : Tendsto (fun k => a (phi k)) atTop (nhds L) :=
    hfull.comp hphi.tendsto_atTop
  have hsub_free' : Tendsto (fun k => a (phi k)) atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
    simpa only [a, Function.comp_apply, spinProdBCF_apply] using hsub_free
  have hL : L = ∫ omega, spinProd A omega
      ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) :=
    tendsto_nhds_unique hsub_L hsub_free'
  simpa only [a, hL] using hfull

end StatMech.FrontierB
