/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanBaseCases.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part35
import Structure.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

theorem finiteExpVarianceSkew_nonpos_of_switchingPairing
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real)
    (hpair : FiniteExpVarianceSkewSwitchingPairing w I r) :
    finiteExpVarianceSkew w I r <= 0 := by
  let S : E × E × E × E -> Real :=
    finiteExpVarianceSkewFourSummand w I r
  have hreindex : (∑ s, S (hpair.switch s)) = ∑ s, S s :=
    Equiv.sum_comp hpair.switch S
  have hpairs : (∑ s, (S s + S (hpair.switch s))) <= 0 := by
    calc
      (∑ s, (S s + S (hpair.switch s))) <= ∑ _s, (0 : Real) :=
        Finset.sum_le_sum fun s _ => hpair.pair_nonpos s
      _ = 0 := by simp
  rw [Finset.sum_add_distrib, hreindex] at hpairs
  have hsum : (∑ s, S s) <= 0 := by linarith
  have hfour :
      (∑ x, ∑ y, ∑ z, ∑ q,
        w x * w y * w z * w q * (I x - I y) ^ 2 *
          (Real.exp (r * (I x + I y - I z - I q)) -
            Real.exp (-r * (I x + I y - I z - I q)))) <= 0 := by
    simpa only [S, finiteExpVarianceSkewFourSummand,
      Fintype.sum_prod_type] using hsum
  have htwice : 2 * finiteExpVarianceSkew w I r <= 0 := by
    rw [two_mul_finiteExpVarianceSkew_eq_fourStateSum]
    exact hfour
  linarith


end
end StatMech.FrontierA
