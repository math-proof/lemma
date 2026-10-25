/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality.Part2
open Equiv SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectBlackBoundaryCycleDualEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectConfigurationBlackBoundaryCycle R omega ≃
      FKRectConfigurationBlackBoundaryCycle R
        (fkRectDualConfigurationEquiv R omega) where
  toFun := Quot.map (fkRectDualBlackDartEquiv R omega) (by
    intro d e hde
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).2
    apply (fkRectDualBlackDartEquiv_reachable_iff R omega d e).2
    exact (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).1 hde)
  invFun := Quot.map (fkRectDualBlackDartEquiv R omega).symm (by
    intro d e hde
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).2
    apply (fkRectDualBlackDartEquiv_reachable_iff R omega
      ((fkRectDualBlackDartEquiv R omega).symm d)
      ((fkRectDualBlackDartEquiv R omega).symm e)).1
    simpa using
      (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).1 hde)
  left_inv := by
    intro C
    induction C using Quot.ind with
    | _ d =>
        apply Quot.sound
        simp
  right_inv := by
    intro C
    induction C using Quot.ind with
    | _ d =>
        apply Quot.sound
        simp

end
end StatMech.FrontierD
