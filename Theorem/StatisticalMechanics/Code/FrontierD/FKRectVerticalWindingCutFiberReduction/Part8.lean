/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPositiveBoundary.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part7
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBlackBoundaryCycleWinding_eq_zero_of_componentHasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnet : FKRectPrimalComponentHasNet R omega K)
    (C : FKRectConfigurationBlackBoundaryCycle R omega)
    (hCK : fkRectBlackBoundaryCyclePrimalComponent R omega C = K) :
    fkRectBlackBoundaryCycleWinding R omega C = 0 := by
  induction C using Quot.ind with
  | _ d =>
    rcases hnet with ⟨p, q, hpq⟩
    let m := permOrbitVisitCount
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)) d.1 d.1
    have hm : 0 < m := permOrbitVisitCount_self_pos _ _
    have hdp :=
      fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
        R omega p d.1
    have hdq :=
      fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
        R omega q d.1
    rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
      R omega d] at hdp hdq
    rw [fkRectBlackBoundaryCycleWinding_mk,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    let c := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    change c = 0
    let u := fkRectWalkWinding R p
    let v := fkRectWalkWinding R q
    change ¬ FKRectWindingIndependent (m • c) u at hdp
    change ¬ FKRectWindingIndependent (m • c) v at hdq
    change FKRectWindingIndependent u v at hpq
    unfold FKRectWindingIndependent at hdp hdq hpq
    push Not at hdp hdq
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul] at hdp hdq
    have hmInt : (m : Int) ≠ 0 := by exact_mod_cast hm.ne'
    have hcu : c.1 * u.2 - c.2 * u.1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hmInt
      calc
        (m : Int) * (c.1 * u.2 - c.2 * u.1) =
            (m : Int) * c.1 * u.2 - (m : Int) * c.2 * u.1 := by ring
        _ = 0 := hdp
    have hcv : c.1 * v.2 - c.2 * v.1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hmInt
      calc
        (m : Int) * (c.1 * v.2 - c.2 * v.1) =
            (m : Int) * c.1 * v.2 - (m : Int) * c.2 * v.1 := by ring
        _ = 0 := hdq
    have hc1mul : c.1 * (u.1 * v.2 - u.2 * v.1) = 0 := by
      calc
        c.1 * (u.1 * v.2 - u.2 * v.1) =
            u.1 * (c.1 * v.2 - c.2 * v.1) -
              v.1 * (c.1 * u.2 - c.2 * u.1) := by ring
        _ = 0 := by rw [hcu, hcv]; ring
    have hc2mul : c.2 * (u.1 * v.2 - u.2 * v.1) = 0 := by
      calc
        c.2 * (u.1 * v.2 - u.2 * v.1) =
            u.2 * (c.1 * v.2 - c.2 * v.1) -
              v.2 * (c.1 * u.2 - c.2 * u.1) := by ring
        _ = 0 := by rw [hcu, hcv]; ring
    have hc1 : c.1 = 0 :=
      (mul_eq_zero.mp hc1mul).resolve_right hpq
    have hc2 : c.2 = 0 :=
      (mul_eq_zero.mp hc2mul).resolve_right hpq
    exact Prod.ext hc1 hc2


theorem fkRectPrimalComponentPositiveBoundaryVerticalMass_eq_zero_of_hasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnet : FKRectPrimalComponentHasNet R omega K) :
    fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K = 0 := by
  classical
  unfold fkRectPrimalComponentPositiveBoundaryVerticalMass
  apply Finset.sum_eq_zero
  intro C _
  by_cases hCK : fkRectBlackBoundaryCyclePrimalComponent R omega C = K
  · rw [if_pos hCK,
      fkRectBlackBoundaryCycleWinding_eq_zero_of_componentHasNet
        R omega K hnet C hCK]
    rfl
  · rw [if_neg hCK]


theorem fkRectPositiveVerticalBoundaryCutFiberBound_of_componentHasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnet : FKRectPrimalComponentHasNet R omega K) :
    fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤
      fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
  rw [fkRectPrimalComponentPositiveBoundaryVerticalMass_eq_zero_of_hasNet
    R omega K hnet]
  exact Nat.zero_le _

end
end StatMech.FrontierD
