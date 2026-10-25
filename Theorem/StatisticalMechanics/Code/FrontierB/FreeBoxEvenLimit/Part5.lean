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
import Def.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part4
open MeasureTheory Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exp_neg_edgeSpinSum_eq_spinProd_sum
    {V : Type*} [DecidableEq V]
    (beta : ℝ) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) (s : ConfigSpace V) :
    Real.exp (-beta * edgeSpinSum F s) =
      ∑ T ∈ F.powerset,
        edgeExpansionCoeff beta F T * spinProd (edgeBoundary (F \ T)) s := by
  unfold edgeSpinSum
  rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [exp_mul_pm (-beta) (bond s _) (bond_eq_pm s _)]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  unfold edgeExpansionCoeff
  rw [Finset.prod_mul_distrib]
  rw [prod_bond_eq_spinProd_edgeBoundary (F \ T)]
  · ring
  · intro e he
    exact hF e (Finset.mem_sdiff.mp he).1

theorem integral_spinProd_sum_tendsto_freeState
    {I : Type*} (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (K : Finset I) (c : I → ℝ) (support : I → Finset (Site d)) :
    Tendsto
      (fun n => ∫ omega, ∑ i ∈ K, c i * spinProd (support i) omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, ∑ i ∈ K, c i * spinProd (support i) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  classical
  have hterm (i : I) (hi : i ∈ K) :
      Tendsto
        (fun n => c i * ∫ omega, spinProd (support i) omega
          ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
        atTop
        (nhds (c i * ∫ omega, spinProd (support i) omega
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) :=
    (integral_freeMeasure_spinProd_tendsto_freeState
      d beta hbeta (support i)).const_mul (c i)
  have hsum := tendsto_finsetSum K hterm
  have hint (mu : Measure (ConfigSpace (Site d))) [IsFiniteMeasure mu] :
      (∫ omega, ∑ i ∈ K, c i * spinProd (support i) omega ∂mu) =
        ∑ i ∈ K, c i * ∫ omega, spinProd (support i) omega ∂mu := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
    · intro i hi
      exact ((spinProdBCF d (support i)).integrable mu).const_mul (c i)
  simpa only [hint] using hsum


theorem integral_exp_neg_edgeSpinSum_tendsto_freeState
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d))) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    Tendsto
      (fun n => ∫ s, Real.exp (-beta * edgeSpinSum F s)
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ s, Real.exp (-beta * edgeSpinSum F s)
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hpoly := integral_spinProd_sum_tendsto_freeState d beta hbeta
    F.powerset (edgeExpansionCoeff beta F)
    (fun T => edgeBoundary (F \ T))
  simpa only [exp_neg_edgeSpinSum_eq_spinProd_sum beta F hF] using hpoly

end StatMech.FrontierB
