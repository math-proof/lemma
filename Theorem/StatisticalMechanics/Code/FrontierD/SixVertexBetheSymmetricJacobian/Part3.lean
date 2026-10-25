/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part4
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBethePositiveHalfScaledJacobianMatrix_eq_mul_diagonal
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    sixVertexBethePositiveHalfScaledJacobianMatrix N m c q =
      sixVertexBethePositiveHalfJacobianMatrix N m c q *
        Matrix.diagonal (sixVertexPositiveHalfRootGap q) := by
  ext j k
  rw [Matrix.mul_diagonal]
  rfl

theorem sixVertexBethePositiveHalfScaledJacobianMatrix_offdiag_nonneg
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    {j k : Fin m} (hjk : j ≠ k) :
    0 ≤ sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k := by
  exact sixVertexBethePositiveHalfJacobianMatrix_mul_gap_offdiag_nonneg
    hc hq _ (fun l => (sixVertexPositiveHalfRootGap_pos_of_open hq l).le) hjk


theorem sixVertexBethePositiveHalfJacobianMatrix_diag
    (N m : Nat) (c : Real) (q : Fin m → Real) (j : Fin m) :
    sixVertexBethePositiveHalfJacobianMatrix N m c q j j =
      (N : Real) +
        ∑ l ∈ Finset.univ.erase (Fin.natAdd m j),
          4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
              (sixVertexEvenSymmetricLift m q l) /
            sixVertexThetaDerivativeDenominator c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j))
              (sixVertexEvenSymmetricLift m q l) -
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) /
            sixVertexThetaDerivativeDenominator c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j))
              (sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev))) := by
  have hcross : Fin.natAdd m j ≠ Fin.castAdd m j.rev := by
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.natAdd, Fin.castAdd] at hval
    omega
  unfold sixVertexBethePositiveHalfJacobianMatrix
  dsimp only
  rw [sixVertexBetheJacobianMatrix, if_pos rfl,
    sixVertexBetheJacobianMatrix, if_neg hcross]


theorem sixVertexBethePositiveHalfScaledJacobianMatrix_diag
    (N m : Nat) (c : Real) (q : Fin m → Real) (j : Fin m) :
    sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j =
      ((N : Real) +
        ∑ l ∈ Finset.univ.erase (Fin.natAdd m j),
          4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
              (sixVertexEvenSymmetricLift m q l) /
            sixVertexThetaDerivativeDenominator c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j))
              (sixVertexEvenSymmetricLift m q l) -
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) /
            sixVertexThetaDerivativeDenominator c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j))
              (sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev)))) *
        sixVertexPositiveHalfRootGap q j := by
  rw [sixVertexBethePositiveHalfScaledJacobianMatrix,
    sixVertexBethePositiveHalfJacobianMatrix_diag]


theorem sixVertexEvenSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance
    {N m : Nat} {c : Real} (hc : 2 < c) (q : Fin m → Real)
    (hgap : ∀ k, sixVertexPositiveHalfRootGap q k ≠ 0)
    (hdom : ∀ j,
      ∑ k ∈ Finset.univ.erase j,
          ‖sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k‖ <
        ‖sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j‖) :
    Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let A := sixVertexBethePositiveHalfJacobianMatrix N m c q
  let D := Matrix.diagonal (sixVertexPositiveHalfRootGap q)
  let B := sixVertexBethePositiveHalfScaledJacobianMatrix N m c q
  have hdetB : Matrix.det B ≠ 0 := det_ne_zero_of_sum_row_lt_diag hdom
  have hBD : B = A * D := by
    exact sixVertexBethePositiveHalfScaledJacobianMatrix_eq_mul_diagonal
      N m c q
  have hdetD : Matrix.det D ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hgap k)
  have hdetA : Matrix.det A ≠ 0 := by
    intro hzero
    apply hdetB
    rw [hBD, Matrix.det_mul, hzero, zero_mul]
  have hmatrix : LinearMap.toMatrix'
      (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap = A := by
    ext j k
    exact sixVertexEvenSymmetricBetheRootJacobian_toMatrix'_apply hc q j k
  have hdetJ : LinearMap.det
      (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap ≠ 0 := by
    rw [← LinearMap.det_toMatrix', hmatrix]
    exact hdetA
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdetJ ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)

end
end StatMech.FrontierD
