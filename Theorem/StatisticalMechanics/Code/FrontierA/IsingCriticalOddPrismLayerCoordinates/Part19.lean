/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part19


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismThreeLayerWeight_swap
    (beta : Real) (n : Nat) (a b : Real)
    (s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismThreeLayerWeight beta n a b s t v =
      oddPrismThreeLayerWeight beta n a b s v t *
        Real.exp ((a - b) *
          (oddPrismLayerSeamInteraction n s t -
            oddPrismLayerSeamInteraction n s v)) := by
  let C := oddPrismLayerHalfWeight beta n s ^ 2 *
    oddPrismUpperConditionedVector beta n v *
    oddPrismUpperConditionedVector beta n t
  rw [show oddPrismThreeLayerWeight beta n a b s t v = C *
      (Real.exp (a * oddPrismLayerSeamInteraction n s t) *
        Real.exp (b * oddPrismLayerSeamInteraction n s v)) by
    unfold oddPrismThreeLayerWeight oddPrismPureSeamKernel C
    ring]
  rw [show oddPrismThreeLayerWeight beta n a b s v t *
      Real.exp ((a - b) *
        (oddPrismLayerSeamInteraction n s t -
          oddPrismLayerSeamInteraction n s v)) = C *
      (Real.exp (a * oddPrismLayerSeamInteraction n s v) *
        Real.exp (b * oddPrismLayerSeamInteraction n s t) *
        Real.exp ((a - b) *
          (oddPrismLayerSeamInteraction n s t -
            oddPrismLayerSeamInteraction n s v))) by
    unfold oddPrismThreeLayerWeight oddPrismPureSeamKernel C
    ring]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem rectangularPrismTransfer_pow_mulVec_boundary_pos
    (beta : Real) (n k : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < ((rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) ^ k) *ᵥ
      rectangularPrismTransferBoundaryVector
        1 beta (2 * n + 1) (2 * n + 1)) s := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  change 0 < ((A ^ k) *ᵥ a) s
  induction k generalizing s with
  | zero =>
      simp only [pow_zero, one_mulVec]
      exact rectangularPrismTransferBoundaryVector_pos
        1 beta (2 * n + 1) (2 * n + 1) s
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_pos
      · intro t _
        exact mul_pos
          (rectangularPrismTransfer_pos
            1 beta (2 * n + 1) (2 * n + 1) s t) (ih t)
      · exact Finset.univ_nonempty

theorem oddPrismUpperConditionedVector_pos
    (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismUpperConditionedVector beta n s := by
  unfold oddPrismUpperConditionedVector oddPrismUpperTransferTail
  exact mul_pos (oddPrismLayerHalfWeight_pos beta n s)
    (rectangularPrismTransfer_pow_mulVec_boundary_pos beta n (n - 1) s)

theorem oddPrismThreeLayerWeight_pos
    (beta : Real) (n : Nat) (a b : Real)
    (s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismThreeLayerWeight beta n a b s v t := by
  unfold oddPrismThreeLayerWeight
  exact mul_pos (mul_pos (mul_pos (mul_pos
    (sq_pos_of_pos (oddPrismLayerHalfWeight_pos beta n s))
    (oddPrismUpperConditionedVector_pos beta n v))
    (oddPrismUpperConditionedVector_pos beta n t))
    (oddPrismPureSeamKernel_pos a n s v))
    (oddPrismPureSeamKernel_pos b n s t)


theorem oddPrismThreeLayerWeight_le_swap
    (beta : Real) (n : Nat) {a b : Real} (hba : b <= a)
    (s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1))
    (hI : oddPrismLayerSeamInteraction n s v <=
      oddPrismLayerSeamInteraction n s t) :
    oddPrismThreeLayerWeight beta n a b s v t <=
      oddPrismThreeLayerWeight beta n a b s t v := by
  have hswap := oddPrismThreeLayerWeight_swap beta n a b s v t
  rw [hswap]
  apply le_mul_of_one_le_right
    (oddPrismThreeLayerWeight_pos beta n a b s v t).le
  apply Real.one_le_exp
  exact mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hI)

theorem oddPrismTransferBridgeRawMoment_eq_threeLayer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      oddPrismThreeLayerRawMoment beta n beta r := by
  unfold oddPrismTransferBridgeRawMoment oddPrismThreeLayerRawMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn s]
  calc
    (∑ t, (oddPrismLayerHalfWeight beta n s ^ 2 *
        ∑ v, oddPrismPureSeamKernel beta n s v *
          oddPrismUpperConditionedVector beta n v) *
        oddPrismUpperConditionedVector beta n t *
        oddPrismPureSeamKernel r n s t) =
      ∑ t, ∑ v, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismUpperConditionedVector beta n v *
        oddPrismUpperConditionedVector beta n t *
        oddPrismPureSeamKernel beta n s v *
        oddPrismPureSeamKernel r n s t := by
          apply Finset.sum_congr rfl
          intro t _
          rw [show (oddPrismLayerHalfWeight beta n s ^ 2 *
              ∑ v, oddPrismPureSeamKernel beta n s v *
                oddPrismUpperConditionedVector beta n v) *
              oddPrismUpperConditionedVector beta n t *
              oddPrismPureSeamKernel r n s t =
            (∑ v, oddPrismPureSeamKernel beta n s v *
                oddPrismUpperConditionedVector beta n v) *
              (oddPrismLayerHalfWeight beta n s ^ 2 *
                oddPrismUpperConditionedVector beta n t *
                oddPrismPureSeamKernel r n s t) by ring]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v _
          ring
    _ = _ := by rw [Finset.sum_comm]


theorem oddPrismThreeLayerRawMoment_symm
    (beta : Real) (n : Nat) (a b : Real) :
    oddPrismThreeLayerRawMoment beta n a b =
      oddPrismThreeLayerRawMoment beta n b a := by
  unfold oddPrismThreeLayerRawMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro v _
  ring


end
end StatMech.FrontierA
