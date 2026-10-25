/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part3
open Filter Finset Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


section CriticalFiniteBox

theorem criticalFiniteBoxPairCorrelation_le_infinite
    (hd : 2 ≤ d) (n : Nat) (x y : sctBox d n) :
    criticalFiniteBoxPairCorrelation d n x y ≤
      currentContinuityFreePairKernel d
        (IsingFK.betaC (magnetization d)) (y.1 - x.1) := by
  by_cases hxy : x = y
  · subst y
    simpa [criticalFiniteBoxPairCorrelation, twoPointJ,
      grahamPairSupport, currentContinuityFreePairKernel] using
      (twoPointJ_self (sctBoxGraph d n)
        (IsingFK.betaC (magnetization d)) (fun _ => 1) x).le
  have hvals : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hsupport :
      boxSpinSupport d n ({x.1, y.1} : Finset (Site d)) =
        ({x, y} : Finset (sctBox d n)) := by
    ext z
    simp only [boxSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hz | hz)
      · exact Or.inl (Subtype.ext hz)
      · exact Or.inr (Subtype.ext hz)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hfinite : criticalFiniteBoxPairCorrelation d n x y =
      currentContinuityFreeBoxTwoPoint d n
        (IsingFK.betaC (magnetization d)) x.1 y.1 := by
    rw [criticalFiniteBoxPairCorrelation,
      expectationJ_one_eq_isingExpectation]
    unfold currentContinuityFreeBoxTwoPoint
    rw [integral_freeMeasure_spinProd d n
      (IsingFK.betaC (magnetization d)) 0 ({x.1, y.1} : Finset (Site d))]
    · rw [hsupport]
      congr 1
      funext sigma
      rw [spinProd_grahamPairSupport]
      simp [spinProd, hxy]
    · intro z hz
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact x.2
      · exact y.2
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  have hdomain := currentContinuityFreeBoxTwoPoint_le_freeTwoPoint
    (IsingFK.betaC (magnetization d)) hbeta n x.1 y.1 (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Ising.mem_boxFinset.mpr x.2
      · exact Ising.mem_boxFinset.mpr y.2)
  rw [hfinite]
  apply hdomain.trans_eq
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (-x.1)
  have hgx : g • x.1 = Percolation.origin d := by
    change -x.1 + x.1 = 0
    rw [neg_add_cancel]
  have hgy : g • y.1 = y.1 - x.1 := by
    change -x.1 + y.1 = y.1 - x.1
    abel
  have himage :
      ({x.1, y.1} : Finset (Site d)).image (fun z => g • z) =
        ({Percolation.origin d, y.1 - x.1} : Finset (Site d)) := by
    simp only [Finset.image_insert, Finset.image_singleton, hgx, hgy]
  have htranslate := integral_freeState_spinProd_translate d
    (IsingFK.betaC (magnetization d)) hbeta g
    ({x.1, y.1} : Finset (Site d))
  rw [himage] at htranslate
  unfold currentContinuityFreeTwoPoint currentContinuityFreePairKernel
  have hdiff : y.1 - x.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hvals)
  rw [if_neg hdiff]
  exact htranslate.symm


end CriticalFiniteBox
end
end StatMech.FrontierA
