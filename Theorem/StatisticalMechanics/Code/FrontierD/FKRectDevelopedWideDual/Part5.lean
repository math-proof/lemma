/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual.Part5
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectDevelopedThreeByOne_faceDualHorizontal_imp_dualHorizontal
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration)
    (hcross : omega ∈
      fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
    fkRectDualConfigurationEquiv R omega ∈
      fkRectDevelopedRectangleHorizontalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n := by
  obtain ⟨x, y, hxy⟩ := hcross
  refine ⟨x, y, ?_⟩
  change ConnectedWithin 2
    (fkRectDevelopedSquarePullback R n
      (fkRectDualConfigurationEquiv R omega))
    (fkRectDevelopedThreeByOneRect n)
    ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩
  exact fkRectDevelopedThreeByOne_faceDual_connectedWithin_imp_dual
    R n hn hwidth hheight omega (by
      simpa [fkRectDevelopedThreeByOneRect] using hxy)


theorem fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n) :
    (fkRectDevelopedRectangleVerticalCrossingEvent
      R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n := by
  intro omega hno
  exact fkRectWide_faceDualHorizontal_of_not_vertical
    (n : Int) (by omega) (fkRectDevelopedSquarePullback R n omega) hno


theorem fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (hface :
      (fkRectDevelopedRectangleVerticalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
    fkRectDualEvent R
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedRectangleHorizontalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n := by
  rintro eta ⟨omega, hno, rfl⟩
  exact fkRectDevelopedThreeByOne_faceDualHorizontal_imp_dualHorizontal
    R n hn hwidth hheight omega (hface hno)


theorem fkRectDevelopedThreeByOne_dualCompl_subset_horizontal
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height) :
    fkRectDualEvent R
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedRectangleHorizontalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n :=
  fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual
    R n hn hwidth hheight
      (fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal R n hn)


theorem fkRectDevelopedThreeByOne_dualPreimageHorizontalCompl_subset_vertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height) :
    fkRectDualPreimageEvent R
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedRectangleVerticalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n := by
  intro omega hnoHorizontal
  by_contra hnoVertical
  have hdualHorizontal :=
    fkRectDevelopedThreeByOne_dualCompl_subset_horizontal
      R n hn hwidth hheight
      (show fkRectDualConfigurationEquiv R omega ∈
        fkRectDualEvent R
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n)ᶜ from
        ⟨omega, hnoVertical, rfl⟩)
  exact hnoHorizontal hdualHorizontal


theorem fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal_of_faceDual
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q)
    (hface :
      (fkRectDevelopedRectangleVerticalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆
      fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
    1 ≤
      fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) +
        q ^ 2 * fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) := by
  let V := fkRectDevelopedRectangleVerticalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  let H := fkRectDevelopedRectangleHorizontalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_le_q_mul_dualEvent R hq Vᶜ
  have hmono := fkRectCriticalEventMass_mono R hq0
    (fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual
      R n hn hwidth hheight hface)
  rw [fkRectCriticalEventMass_compl R hq0 V] at hdual
  have hlinear : 1 - fkRectCriticalEventMass R q V ≤
      q * fkRectCriticalEventMass R q H :=
    hdual.trans (mul_le_mul_of_nonneg_left hmono hq0.le)
  have hqSq : q ≤ q ^ 2 := by nlinarith
  have hHnonneg : 0 ≤ fkRectCriticalEventMass R q H :=
    fkRectCriticalEventMass_nonneg R hq0 H
  have hweaken : q * fkRectCriticalEventMass R q H ≤
      q ^ 2 * fkRectCriticalEventMass R q H :=
    mul_le_mul_of_nonneg_right hqSq hHnonneg
  dsimp only [V, H] at hlinear hweaken ⊢
  linarith


theorem fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 ≤
      fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) +
        q ^ 2 * fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) :=
  fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal_of_faceDual
    R n hn hwidth hheight hq
      (fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal R n hn)


theorem fkRectCritical_one_le_threeByOneHorizontal_add_q_sq_mul_vertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 ≤
      fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) +
        q ^ 2 * fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) := by
  let H := fkRectDevelopedRectangleHorizontalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  let V := fkRectDevelopedRectangleVerticalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  let A := fkRectDualPreimageEvent R Hᶜ
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_dualEvent_le R hq A
  have hdualEq : fkRectDualEvent R A = Hᶜ :=
    fkRectDualEvent_dualPreimageEvent R Hᶜ
  rw [hdualEq, fkRectCriticalEventMass_compl R hq0 H] at hdual
  have hmono := fkRectCriticalEventMass_mono R hq0
    (fkRectDevelopedThreeByOne_dualPreimageHorizontalCompl_subset_vertical
      R n hn hwidth hheight)
  have hlinear : 1 - fkRectCriticalEventMass R q H ≤
      q * fkRectCriticalEventMass R q V :=
    hdual.trans (mul_le_mul_of_nonneg_left hmono hq0.le)
  have hqSq : q ≤ q ^ 2 := by nlinarith
  have hV0 : 0 ≤ fkRectCriticalEventMass R q V :=
    fkRectCriticalEventMass_nonneg R hq0 V
  have hweaken : q * fkRectCriticalEventMass R q V ≤
      q ^ 2 * fkRectCriticalEventMass R q V :=
    mul_le_mul_of_nonneg_right hqSq hV0
  dsimp only [H, V] at hlinear hweaken ⊢
  linarith

end
end StatMech.FrontierD
