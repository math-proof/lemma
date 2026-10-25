/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfinitePlusFreeSourceSwitching
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceZeroBeta
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.Sharpness.IsingMagnetizationZero
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Def.StatisticalMechanics.Code.FrontierB.CurrentContinuityReduction
open Filter MeasureTheory Set Topology BoundedContinuousFunction


namespace StatMech.FrontierB

open Ising Lattice Percolation Sharpness

variable {d : ℕ}


theorem independentSuperposedTraceLaw_real_apply
    {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E))
    {A : Set (ConfigSpace E)} (hA : MeasurableSet A) :
    (independentSuperposedTraceLaw mu nu : Measure _).real A =
      (mu.prod nu : Measure _).real (superposedCurrentTrace ⁻¹' A) := by
  have hleft : (((independentSuperposedTraceLaw mu nu) A : NNReal) : ℝ) =
      (independentSuperposedTraceLaw mu nu : Measure _).real A := by
    rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  have hright : ((mu.prod nu (superposedCurrentTrace ⁻¹' A) : NNReal) : ℝ) =
      (mu.prod nu : Measure _).real (superposedCurrentTrace ⁻¹' A) := by
    rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft, ← hright]
  exact congrArg (fun z : NNReal => (z : ℝ))
    (ProbabilityMeasure.map_apply (mu.prod nu)
      continuous_superposedCurrentTrace.measurable.aemeasurable hA)


theorem currentContinuity_mixed_twoPoint_identity
    (beta : ℝ) (hbeta : 0 < beta)
    (hunique :
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _)
        (atLeastTwoInfinite d) = 0)
    (x y : Site d) (hxy : x ≠ y) :
    currentContinuityPlusTwoPoint d beta x y *
        currentContinuityFreeTwoPoint d beta x y =
      StatMech.FK.infiniteTwoPointReal
        (currentContinuityMixedTraceLaw d beta hbeta : Measure _) x y := by
  obtain ⟨N, hN⟩ := Percolation.finite_subset_box
    ({x, y} : Set (Site d)) (Set.toFinite _)
  have hx : x ∈ box d N := hN (by simp)
  have hy : y ∈ box d N := hN (by simp)
  have hswitch := infinitePlusFreeSource_switching_of_uniqueInfiniteCluster
    d N beta hbeta x y hx hy hxy hunique Set.univ isClopen_univ
  simp only [Set.preimage_univ, probReal_univ, mul_one] at hswitch
  unfold currentContinuityPlusTwoPoint currentContinuityFreeTwoPoint
    StatMech.FK.infiniteTwoPointReal currentContinuityMixedTraceLaw
  rw [independentSuperposedTraceLaw_real_apply _ _
    (measurableSet_connected x y)]
  simpa [currentPairTraceConnectionGate] using hswitch


theorem currentContinuityPlusTwoPoint_eq_plusCorr
    (beta : ℝ) (x y : Site d) (hxy : x ≠ y) :
    currentContinuityPlusTwoPoint d beta x y = plusCorr d beta x y := by
  unfold currentContinuityPlusTwoPoint plusCorr
  congr 1
  funext omega
  simp [spinProd, hxy]


theorem currentContinuity_no_persistent_connectivity_of_freeLROZero
    (beta : ℝ) (hbeta : 0 < beta)
    (hunique :
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _)
        (atLeastTwoInfinite d) = 0)
    (hLRO : CurrentContinuityFreeLROZero d beta) :
    ¬ CurrentContinuityConnectivityPersists d
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
  rintro ⟨epsilon, hepsilon, hpersist⟩
  obtain ⟨R, hR⟩ := hLRO epsilon hepsilon
  obtain ⟨x, hxout, hxlower⟩ := hpersist R
  have hxo : Percolation.origin d ≠ x := by
    intro h
    subst x
    exact hxout (origin_mem_box' R)
  have hid := currentContinuity_mixed_twoPoint_identity
    beta hbeta hunique (Percolation.origin d) x hxo
  have hplus0 :
      0 ≤ currentContinuityPlusTwoPoint d beta (Percolation.origin d) x := by
    rw [currentContinuityPlusTwoPoint_eq_plusCorr beta _ _ hxo]
    exact plusCorr_nonneg beta hbeta.le _ _
  have hplus1 :
      currentContinuityPlusTwoPoint d beta (Percolation.origin d) x ≤ 1 := by
    rw [currentContinuityPlusTwoPoint_eq_plusCorr beta _ _ hxo]
    exact plusCorr_le_one beta _ _
  have hfree := hR x hxout
  have habs :
      |currentContinuityPlusTwoPoint d beta (Percolation.origin d) x *
        currentContinuityFreeTwoPoint d beta (Percolation.origin d) x| < epsilon := by
    rw [abs_mul, abs_of_nonneg hplus0]
    calc
      currentContinuityPlusTwoPoint d beta (Percolation.origin d) x *
          |currentContinuityFreeTwoPoint d beta (Percolation.origin d) x|
          ≤ 1 * |currentContinuityFreeTwoPoint d beta (Percolation.origin d) x| :=
        mul_le_mul_of_nonneg_right hplus1 (abs_nonneg _)
      _ < 1 * epsilon := mul_lt_mul_of_pos_left hfree zero_lt_one
      _ = epsilon := one_mul _
  rw [hid] at habs
  unfold StatMech.FK.infiniteTwoPointReal at habs
  rw [abs_of_nonneg measureReal_nonneg] at habs
  exact (not_lt_of_ge hxlower) habs


theorem currentContinuity_no_percolation_of_freeLROZero
    (beta : ℝ) (hbeta : 0 < beta)
    (hunique :
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _)
        (atLeastTwoInfinite d) = 0)
    (hprinciple : CurrentContinuityPercolationPrinciple d
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _))
    (hLRO : CurrentContinuityFreeLROZero d beta) :
    (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
      (percolationEvent d) = 0 := by
  apply le_antisymm
  · by_contra hne
    have hpos : 0 < (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
        (percolationEvent d) := lt_of_not_ge hne
    exact currentContinuity_no_persistent_connectivity_of_freeLROZero
      beta hbeta hunique hLRO (hprinciple hpos)
  · exact measureReal_nonneg


theorem currentContinuity_freePlus_no_percolation_zero_beta :
    (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d 0 le_rfl)
      (infiniteFreeCurrentMeasure d 0 le_rfl) : Measure _).real
        (percolationEvent d) = 0 := by
  rw [independentSuperposedTraceLaw_comm
    (infinitePlusCurrentMeasure d 0 le_rfl)
    (infiniteFreeCurrentMeasure d 0 le_rfl)]
  rw [freePlusSuperposedTraceLaw_zero_beta]
  have hmeas : MeasurableSet (percolationEvent d) := by
    change MeasurableSet (StatMech.FK.clusterInfiniteEvent d (Percolation.origin d))
    exact StatMech.FK.measurableSet_clusterInfiniteEvent (Percolation.origin d)
  unfold Measure.real
  have heval : (Measure.dirac
      (fun _ => false : ConfigSpace (Sym2 (Site d)))) (percolationEvent d) = 0 := by
    rw [Measure.dirac_apply'
      (fun _ => false : ConfigSpace (Sym2 (Site d))) hmeas]
    simp [mem_percolationEvent, cluster_allClosed]
  rw [heval]
  simp


end StatMech.FrontierB
