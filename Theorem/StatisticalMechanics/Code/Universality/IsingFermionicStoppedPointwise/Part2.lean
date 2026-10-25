/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise


namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

theorem isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t p' q| <=
      (Nat.card
        (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) : Real) /
          (4 : Real) ^ t := by
  classical
  letI := Fintype.ofFinite (IsingLeapfrogChoiceStringFamily t)
  let e := isingLeapfrogCouplingChoiceEquiv t
    (isingLeapfrogBoxInt p) level
  let f : IsingLeapfrogChoiceStringFamily t -> IsingLeapfrogBox R :=
    fun w => isingLeapfrogChoiceRun R p w.1
  let g : IsingLeapfrogChoiceStringFamily t -> IsingLeapfrogBox R :=
    fun w => isingLeapfrogChoiceRun R p' w.1
  have hcount := finiteUniformCoupling_fiber_abs_le_badAt e f g q
  have hden : 0 < (4 : Real) ^ t := by positivity
  have hfiber :
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p q) =
        Nat.card {w : IsingLeapfrogChoiceStringFamily t // f w = q} :=
    Nat.card_congr (isingLeapfrogStoppedChoicePathFiberEquiv R t p q)
  have hfiber' :
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p' q) =
        Nat.card {w : IsingLeapfrogChoiceStringFamily t // g w = q} :=
    Nat.card_congr (isingLeapfrogStoppedChoicePathFiberEquiv R t p' q)
  simp_rw [isingLeapfrogStoppedKernel_eq_natCard_choicePath_div]
  rw [hfiber, hfiber', div_sub_div_same, abs_div, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  simpa only [e, f, g, IsingLeapfrogStoppedCouplingBadAtFamily] using hcount


theorem isingLeapfrogExitKernel_reflectionCoupling_abs_le_badAt
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    |isingLeapfrogExitKernel R t p q -
        isingLeapfrogExitKernel R t p' q| <=
      (Nat.card
        (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) : Real) /
          (4 : Real) ^ t := by
  by_cases hq : isingLeapfrogBoxBoundary R q
  · simpa [isingLeapfrogExitKernel, hq] using
      isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt
        R t p p' q level
  · simp only [isingLeapfrogExitKernel, hq, if_false, sub_self, abs_zero]
    positivity


end StatMech.Universality
