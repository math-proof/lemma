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
import Def.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part5
open MeasureTheory Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem spinProd_eq_plusSpinExpansion {d : ℕ}
    (A : Finset (Site d)) (omega : ConfigSpace (Site d)) :
    spinProd A omega =
      ∑ T ∈ A.powerset,
        plusSpinExpansionCoeff A T * iti_monomialBcf T omega := by
  unfold spinProd
  have hspin (x : Site d) :
      spin omega x = 2 * pstc_coordCM x omega + (-1 : ℝ) := by
    simp only [pstc_coordCM_apply]
    by_cases hx : omega x
    · simp [spin, hx]
      norm_num
    · simp [spin, hx]
  simp_rw [hspin]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  unfold plusSpinExpansionCoeff
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
  have hmono : (∏ x ∈ T, pstc_coordCM x omega) =
      iti_monomialBcf T omega := by
    change (∏ x ∈ T, pstc_coordCM x omega) = iti_monomialCM T omega
    rw [iti_monomialCM, ContinuousMap.prod_apply]
  rw [hmono]
  ring

theorem integral_plusMeasure_spinProd_full_tendsto
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : Finset (Site d)) :
    Tendsto
      (fun n => ∫ omega, spinProd A omega
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd A omega
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  have hterm (T : Finset (Site d)) (hT : T ∈ A.powerset) :
      Tendsto
        (fun n => plusSpinExpansionCoeff A T *
          (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real
            (StatMech.FK.fmu_multiOpen T))
        atTop
        (nhds (plusSpinExpansionCoeff A T *
          (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
            (StatMech.FK.fmu_multiOpen T))) :=
    (itb_plus_multiOpen_full_tendsto hbeta le_rfl T hphi hconv).const_mul _
  have hsum := tendsto_finset_sum A.powerset hterm
  have hint (mu : Measure (ConfigSpace (Site d))) [IsFiniteMeasure mu] :
      (∫ omega, spinProd A omega ∂mu) =
        ∑ T ∈ A.powerset, plusSpinExpansionCoeff A T *
          mu.real (StatMech.FK.fmu_multiOpen T) := by
    simp_rw [spinProd_eq_plusSpinExpansion A]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro T hT
      rw [integral_const_mul, iti_integral_monomialBcf]
    · intro T hT
      exact ((iti_monomialBcf T).integrable mu).const_mul _
  simpa only [hint] using hsum

theorem integral_plusMeasure_exp_neg_edgeSpinSum_full_tendsto
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d))) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    Tendsto
      (fun n => ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hterm (T : Finset (Sym2 (Site d))) (hT : T ∈ F.powerset) :
      Tendsto
        (fun n => edgeExpansionCoeff beta F T *
          ∫ omega, spinProd (edgeBoundary (F \ T)) omega
            ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
        atTop
        (nhds (edgeExpansionCoeff beta F T *
          ∫ omega, spinProd (edgeBoundary (F \ T)) omega
            ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) :=
    (integral_plusMeasure_spinProd_full_tendsto d beta hbeta _).const_mul _
  have hsum := tendsto_finset_sum F.powerset hterm
  have hint (mu : Measure (ConfigSpace (Site d))) [IsFiniteMeasure mu] :
      (∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu) =
        ∑ T ∈ F.powerset, edgeExpansionCoeff beta F T *
          ∫ omega, spinProd (edgeBoundary (F \ T)) omega ∂mu := by
    simp_rw [exp_neg_edgeSpinSum_eq_spinProd_sum beta F hF]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro T hT
      rw [integral_const_mul]
    · intro T hT
      exact ((spinProdBCF d (edgeBoundary (F \ T))).integrable mu).const_mul _
  simpa only [hint] using hsum

end StatMech.FrontierB
