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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part26


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismTransferFlippedTiltedPairWeight_pos
    (beta : Real) (n : Nat) (r : Real)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismTransferFlippedTiltedPairWeight beta n r x := by
  unfold oddPrismTransferFlippedTiltedPairWeight
  exact mul_pos (mul_pos
    (oddPrismLowerConditionedVector_pos beta n x.1)
    (oddPrismUpperConditionedVector_pos beta n (FieldGhostDict.flipV x.2)))
    (oddPrismPureSeamKernel_pos r n x.1 x.2)


theorem oddPrismTransferTiltedPairWeight_flip_cross
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r)
    (n : Nat) (hn : 0 < n)
    (x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferTiltedPairWeight beta n r y <=
      oddPrismTransferFlippedTiltedPairWeight beta n r (x ⊓ y) *
        oddPrismTransferTiltedPairWeight beta n r (x ⊔ y) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  have hl := oddPrismLowerConditionedVector_logSupermodular
    hbeta n hn s t
  have hu := oddPrismUpperConditionedVector_flip_cross hbeta n v w
  have hk := oddPrismPureSeamKernel_pair_logSupermodular hr n s t v w
  have hl0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismLowerConditionedVector beta n a :=
    (oddPrismLowerConditionedVector_pos beta n a).le
  have hu0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismUpperConditionedVector beta n a :=
    (oddPrismUpperConditionedVector_pos beta n a).le
  have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismPureSeamKernel r n a b :=
    (oddPrismPureSeamKernel_pos r n a b).le
  unfold oddPrismTransferFlippedTiltedPairWeight
    oddPrismTransferTiltedPairWeight oddPrismTransferPairBaseWeight
  calc
    (oddPrismLowerConditionedVector beta n s *
          oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV v) *
          oddPrismPureSeamKernel r n s v) *
        (oddPrismLowerConditionedVector beta n t *
          oddPrismUpperConditionedVector beta n w *
          oddPrismPureSeamKernel r n t w) =
      (oddPrismLowerConditionedVector beta n s *
          oddPrismLowerConditionedVector beta n t) *
        (oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV v) *
          oddPrismUpperConditionedVector beta n w) *
        (oddPrismPureSeamKernel r n s v *
          oddPrismPureSeamKernel r n t w) := by ring
    _ <=
      (oddPrismLowerConditionedVector beta n (s ⊓ t) *
          oddPrismLowerConditionedVector beta n (s ⊔ t)) *
        (oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) *
        (oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w)) := by
      have hk' : oddPrismPureSeamKernel r n s v *
            oddPrismPureSeamKernel r n t w <=
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) *
            oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) := by
        simpa only [mul_comm] using hk
      have hLU :
          (oddPrismLowerConditionedVector beta n s *
              oddPrismLowerConditionedVector beta n t) *
            (oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV v) *
              oddPrismUpperConditionedVector beta n w) <=
          (oddPrismLowerConditionedVector beta n (s ⊓ t) *
              oddPrismLowerConditionedVector beta n (s ⊔ t)) *
            (oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (v ⊓ w)) *
              oddPrismUpperConditionedVector beta n (v ⊔ w)) := by
        apply mul_le_mul hl hu
        · exact mul_nonneg (hu0 (FieldGhostDict.flipV v)) (hu0 w)
        · exact mul_nonneg (hl0 (s ⊓ t)) (hl0 (s ⊔ t))
      apply mul_le_mul hLU hk'
      · exact mul_nonneg (hk0 s v) (hk0 t w)
      · exact mul_nonneg
          (mul_nonneg (hl0 (s ⊓ t)) (hl0 (s ⊔ t)))
          (mul_nonneg (hu0 (FieldGhostDict.flipV (v ⊓ w))) (hu0 (v ⊔ w)))
    _ =
      (oddPrismLowerConditionedVector beta n (s ⊓ t) *
          oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w)) *
        (oddPrismLowerConditionedVector beta n (s ⊔ t) *
          oddPrismUpperConditionedVector beta n (v ⊔ w) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w)) := by ring

theorem oddPrismTransferBridgeFlippedRawMoment_eq_sum_pairWeight
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeFlippedRawMoment beta n r =
      ∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x := by
  unfold oddPrismTransferBridgeFlippedRawMoment
    oddPrismTransferFlippedTiltedPairWeight
  rw [Fintype.sum_prod_type]

end
end StatMech.FrontierA
