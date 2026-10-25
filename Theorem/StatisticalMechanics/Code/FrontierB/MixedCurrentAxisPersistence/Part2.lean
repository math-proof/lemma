/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentChainClosure
import Def.StatisticalMechanics.Code.FrontierB.MixedCurrentAxisPersistence.Part2
open Filter MeasureTheory Set Topology
open scoped symmDiff


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation Sharpness

open StatMech.OSSS.FKSharpnessWeightedPhaseTransport

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


theorem currentContinuityAxisPercolationPrinciple_of_mixing
    (d : Nat) (hd : 1 ≤ d)
    (rho : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (rho : Measure (ConfigSpace (Sym2 (Site d)))))
    (hmix : fmu_AxisCofinalGenMixing
      (fun k => FK.freeAxisTranslationPower hd k)
      (rho : Measure (ConfigSpace (Sym2 (Site d)))))
    (hunique : (rho : Measure (ConfigSpace (Sym2 (Site d))))
      (atLeastTwoInfinite d) = 0) :
    CurrentContinuityAxisPercolationPrinciple d hd
      (rho : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro htheta
  let theta := (rho : Measure (ConfigSpace (Sym2 (Site d)))).real
    (percolationEvent d)
  let epsilon := theta ^ 2 / 2
  have htheta' : 0 < theta := htheta
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  refine ⟨epsilon, hepsilon, ?_⟩
  intro K
  let tolerance := theta ^ 2 / 20
  have htolerance : 0 < tolerance := by dsimp [tolerance]; positivity
  let E := clusterInfiniteEvent d (origin d)
  have hEmeas : MeasurableSet E :=
    measurableSet_clusterInfiniteEvent (origin d)
  obtain ⟨k, hk, hcorr⟩ := fmu_axisCofinal_event_exists_after
    (fun k => FK.freeAxisTranslationPower hd k) hti hmix E hEmeas
      K tolerance htolerance
  refine ⟨k, hk, ?_⟩
  have hEmass : (rho : Measure (ConfigSpace (Sym2 (Site d)))).real E =
      theta := rfl
  have hshift :
      (shift (FK.freeAxisTranslationPower hd k) :
        ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' E =
        clusterInfiniteEvent d (currentContinuityAxisSite hd k) := by
    simpa [E, currentContinuityAxisSite] using
      (shift_preimage_clusterInfiniteEvent (d := d)
        (FK.freeAxisTranslationPower hd k)
        (currentContinuityAxisSite hd k))
  have hcorrLower : epsilon ≤
      (rho : Measure (ConfigSpace (Sym2 (Site d)))).real
        (E ∩ (shift (FK.freeAxisTranslationPower hd k)) ⁻¹' E) := by
    have habs := (abs_lt.mp hcorr).1
    rw [hEmass] at habs
    dsimp [epsilon, tolerance] at habs ⊢
    nlinarith [sq_pos_of_pos htheta']
  rw [hshift] at hcorrLower
  exact hcorrLower.trans
    (infinite_cluster_inter_le_twoPoint
      (rho : Measure (ConfigSpace (Sym2 (Site d)))) hunique
      (origin d) (currentContinuityAxisSite hd k))

theorem currentContinuityMixedTraceLaw_axisPercolationPrinciple
    (d : Nat) (hd : 1 ≤ d) (beta : Real) (hbeta : 0 < beta) :
    CurrentContinuityAxisPercolationPrinciple d hd
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
  apply currentContinuityAxisPercolationPrinciple_of_mixing
    d hd (currentContinuityMixedTraceLaw d beta hbeta)
    (currentContinuityMixedTraceLaw_isTranslationInvariant d beta hbeta)
  · rw [show currentContinuityMixedTraceLaw d beta hbeta =
        independentSuperposedTraceLaw
          (infiniteFreeCurrentMeasure d beta hbeta.le)
          (infinitePlusCurrentMeasure d beta hbeta.le) by
      exact independentSuperposedTraceLaw_comm _ _]
    exact freePlusSuperposedTraceLaw_axisCofinalGenMixing hd hbeta
  · exact currentContinuityMixedTraceLaw_uniqueInfiniteCluster
      d hd beta hbeta


theorem currentContinuity_no_axis_persistent_connectivity_of_freeAxisLROZero
    {d : Nat} (hd : 1 ≤ d) (beta : Real) (hbeta : 0 < beta)
    (hunique :
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _)
        (atLeastTwoInfinite d) = 0)
    (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
    ¬ CurrentContinuityAxisConnectivityPersists d hd
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
  rintro ⟨epsilon, hepsilon, hpersist⟩
  obtain ⟨K, hK⟩ := hLRO epsilon hepsilon
  obtain ⟨k, hk, hklower⟩ := hpersist (max K 1)
  have hkK : K ≤ k := (le_max_left K 1).trans hk
  have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
  have hxo : origin d ≠ currentContinuityAxisSite hd k := by
    intro h
    have hcoord := congrFun h ⟨0, hd⟩
    simp [currentContinuityAxisSite, FK.freeAxisTranslationPower,
      smul_site_apply, origin] at hcoord
    omega
  have hid := currentContinuity_mixed_twoPoint_identity
    beta hbeta hunique (origin d) (currentContinuityAxisSite hd k) hxo
  have hplus0 : 0 ≤ currentContinuityPlusTwoPoint d beta (origin d)
      (currentContinuityAxisSite hd k) := by
    rw [currentContinuityPlusTwoPoint_eq_plusCorr beta _ _ hxo]
    exact Sharpness.plusCorr_nonneg beta hbeta.le _ _
  have hplus1 : currentContinuityPlusTwoPoint d beta (origin d)
      (currentContinuityAxisSite hd k) ≤ 1 := by
    rw [currentContinuityPlusTwoPoint_eq_plusCorr beta _ _ hxo]
    exact Sharpness.plusCorr_le_one beta _ _
  have hfree := hK k hkK
  have habs :
      |currentContinuityPlusTwoPoint d beta (origin d)
          (currentContinuityAxisSite hd k) *
        currentContinuityFreeTwoPoint d beta (origin d)
          (currentContinuityAxisSite hd k)| < epsilon := by
    rw [abs_mul, abs_of_nonneg hplus0]
    calc
      currentContinuityPlusTwoPoint d beta (origin d)
            (currentContinuityAxisSite hd k) *
          |currentContinuityFreeTwoPoint d beta (origin d)
            (currentContinuityAxisSite hd k)|
          ≤ 1 * |currentContinuityFreeTwoPoint d beta (origin d)
            (currentContinuityAxisSite hd k)| :=
        mul_le_mul_of_nonneg_right hplus1 (abs_nonneg _)
      _ < 1 * epsilon := mul_lt_mul_of_pos_left hfree zero_lt_one
      _ = epsilon := one_mul _
  rw [hid] at habs
  unfold infiniteTwoPointReal at habs
  rw [abs_of_nonneg measureReal_nonneg] at habs
  exact (not_lt_of_ge hklower) habs


theorem currentContinuity_no_percolation_of_freeAxisLROZero
    {d : Nat} (hd : 1 ≤ d) (beta : Real) (hbeta : 0 < beta)
    (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
    (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
      (percolationEvent d) = 0 := by
  apply le_antisymm
  · by_contra hne
    have hpos : 0 <
        (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
          (percolationEvent d) := lt_of_not_ge hne
    exact currentContinuity_no_axis_persistent_connectivity_of_freeAxisLROZero
      hd beta hbeta
      (currentContinuityMixedTraceLaw_uniqueInfiniteCluster d hd beta hbeta)
      hLRO
      (currentContinuityMixedTraceLaw_axisPercolationPrinciple
        d hd beta hbeta hpos)
  · exact measureReal_nonneg

end StatMech.FrontierB
