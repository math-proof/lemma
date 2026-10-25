/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientedSplit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientationWordExpansion
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem matrixOrientationWordProduct_zero
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (B : Matrix alpha alpha Real) (word : Fin 0 -> Bool) :
    matrixOrientationWordProduct B 0 word = 1 := rfl

@[simp] theorem matrixOrientationWordProduct_cons
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (B : Matrix alpha alpha Real) (M : Nat) (b : Bool)
    (word : Fin M -> Bool) :
    matrixOrientationWordProduct B (M + 1) (Fin.cons b word) =
      (if b then B else Bᵀ) *
        matrixOrientationWordProduct B M word := by
  simp [matrixOrientationWordProduct]

theorem sum_matrixOrientationWordProduct_succ
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (B : Matrix alpha alpha Real) (M : Nat) :
    (∑ word : Fin (M + 1) -> Bool,
        matrixOrientationWordProduct B (M + 1) word) =
      (B + Bᵀ) *
        ∑ word : Fin M -> Bool,
          matrixOrientationWordProduct B M word := by
  classical
  calc
    (∑ word : Fin (M + 1) -> Bool,
        matrixOrientationWordProduct B (M + 1) word) =
        ∑ bw : Bool × (Fin M -> Bool),
          matrixOrientationWordProduct B (M + 1)
            (Fin.cons bw.1 bw.2) := by
      symm
      apply Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (M + 1) => Bool)
      intro bw
      rfl
    _ = ∑ b : Bool, ∑ word : Fin M -> Bool,
          (if b then B else Bᵀ) *
            matrixOrientationWordProduct B M word := by
      rw [Fintype.sum_prod_type]
      simp only [matrixOrientationWordProduct_cons]
    _ = ∑ b : Bool, (if b then B else Bᵀ) *
          ∑ word : Fin M -> Bool,
            matrixOrientationWordProduct B M word := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
    _ = (B + Bᵀ) *
          ∑ word : Fin M -> Bool,
            matrixOrientationWordProduct B M word := by
      simp only [Fintype.sum_bool]
      noncomm_ring


theorem add_transpose_pow_eq_sum_orientationWords
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (B : Matrix alpha alpha Real) (M : Nat) :
    (B + Bᵀ) ^ M =
      ∑ word : Fin M -> Bool,
        matrixOrientationWordProduct B M word := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [pow_succ']
      rw [ih]
      exact (sum_matrixOrientationWordProduct_succ B M).symm


theorem sixVertexSectorTransfer_pow_eq_sum_orientationWords
    (N n M : Nat) (c : Real) :
    sixVertexSectorTransfer N n c ^ M =
      ∑ word : Fin M -> Bool,
        matrixOrientationWordProduct
          (sixVertexSectorForwardTransfer N n c) M word := by
  rw [sixVertexSectorTransfer_eq_forward_add_transpose]
  exact add_transpose_pow_eq_sum_orientationWords
    (sixVertexSectorForwardTransfer N n c) M


theorem trace_sixVertexSectorTransfer_pow_eq_sum_orientationWords
    (N n M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N n c ^ M) =
      ∑ word : Fin M -> Bool,
        Matrix.trace (matrixOrientationWordProduct
          (sixVertexSectorForwardTransfer N n c) M word) := by
  rw [sixVertexSectorTransfer_pow_eq_sum_orientationWords]
  exact Matrix.trace_sum Finset.univ fun word =>
    matrixOrientationWordProduct
      (sixVertexSectorForwardTransfer N n c) M word


end
end StatMech.FrontierD
