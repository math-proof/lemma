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
import Def.StatisticalMechanics.Code.FrontierB.CurrentContinuityReduction.Part2
open Filter MeasureTheory Set Topology BoundedContinuousFunction


namespace StatMech.FrontierB

open Ising Lattice Percolation Sharpness

variable {d : ℕ}


theorem currentContinuity_twoPoint_eq_of_no_percolation
    (beta : ℝ) (hbeta : 0 < beta)
    (hinfluence : CurrentContinuityTwoPointInfluenceBound d beta hbeta)
    (hnoperco : (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
      (percolationEvent d) = 0) (x y : Site d) :
    currentContinuityPlusTwoPoint d beta x y =
      currentContinuityFreeTwoPoint d beta x y := by
  obtain ⟨C, _hC, hinfluence⟩ := hinfluence
  have h := hinfluence x y
  rw [hnoperco] at h
  simp only [mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))


theorem currentContinuity_magnetization_eq_zero
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hLRO : CurrentContinuityFreeLROZero d beta)
    (htwo : ∀ x : Site d,
      currentContinuityPlusTwoPoint d beta (Percolation.origin d) x =
        currentContinuityFreeTwoPoint d beta (Percolation.origin d) x)
    (hd : 1 ≤ d) :
    magnetization d beta = 0 := by
  have hsquare : magnetization d beta ^ 2 ≤ 0 := by
    by_contra hnot
    have hsqpos : 0 < magnetization d beta ^ 2 := lt_of_not_ge hnot
    obtain ⟨R, hR⟩ := hLRO (magnetization d beta ^ 2 / 2) (by positivity)
    let i : Fin d := ⟨0, hd⟩
    let x : Site d := fun j => if j = i then Int.ofNat (R + 1) else 0
    have hxout : x ∉ box d R := by
      intro hx
      have := hx i
      simp [x, i] at this
      omega
    have hxo : Percolation.origin d ≠ x := by
      intro heq
      have := congrFun heq i
      simp [x, i, Percolation.origin] at this
      omega
    have hbound :=
      magnetization_sq_le_plusCorr beta hbeta (Percolation.origin d) x
    rw [← currentContinuityPlusTwoPoint_eq_plusCorr beta _ _ hxo, htwo x] at hbound
    have hsmall := hR x hxout
    have hnonneg :
        0 ≤ currentContinuityFreeTwoPoint d beta (Percolation.origin d) x :=
      htwo x ▸ (by
        rw [currentContinuityPlusTwoPoint_eq_plusCorr beta _ _ hxo]
        exact plusCorr_nonneg beta hbeta _ _)
    rw [abs_of_nonneg hnonneg] at hsmall
    linarith
  nlinarith [sq_nonneg (magnetization d beta)]


theorem currentContinuity_core_of_probabilistic_inputs
    (beta : ℝ) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hunique :
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _)
        (atLeastTwoInfinite d) = 0)
    (hprinciple : CurrentContinuityPercolationPrinciple d
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _))
    (hinfluence : CurrentContinuityTwoPointInfluenceBound d beta hbeta)
    (hLRO : CurrentContinuityFreeLROZero d beta) :
    (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
          (percolationEvent d) = 0 ∧
      (∀ x y : Site d,
        currentContinuityPlusTwoPoint d beta x y =
          currentContinuityFreeTwoPoint d beta x y) ∧
      magnetization d beta = 0 := by
  have hnoperco := currentContinuity_no_percolation_of_freeLROZero
    beta hbeta hunique hprinciple hLRO
  have htwo : ∀ x y : Site d,
      currentContinuityPlusTwoPoint d beta x y =
        currentContinuityFreeTwoPoint d beta x y :=
    fun x y => currentContinuity_twoPoint_eq_of_no_percolation
      beta hbeta hinfluence hnoperco x y
  exact ⟨hnoperco, htwo,
    currentContinuity_magnetization_eq_zero beta hbeta.le hLRO
      (fun x => htwo (Percolation.origin d) x) hd⟩


theorem currentContinuity_localExpectation_tendsto_of_unique_limit
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (mu : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (muLim : ProbabilityMeasure (ConfigSpace (Site d)))
    (hconv : WeakConvergesTo mu muLim)
    (hDLR : IsDLRState d beta 0 (muLim : Measure _))
    (hphase : (plusState d beta 0 : Measure (ConfigSpace (Site d))) =
      (minusState d beta 0 : Measure (ConfigSpace (Site d))))
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    Tendsto (fun n => ∫ omega, f omega ∂(mu n : Measure _)) atTop
      (nhds (∫ omega, f omega
        ∂(minusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hlim : (muLim : Measure (ConfigSpace (Site d))) =
      (minusState d beta 0 : Measure (ConfigSpace (Site d))) :=
    gsi_gibbs_unique_of_phases_eq beta 0 hbeta le_rfl _ hDLR hphase
  have h := hconv.tendsto_integral f
  simpa [hlim] using h

end StatMech.FrontierB
