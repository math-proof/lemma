/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.PositiveTransferPerron
open Finset Matrix Filter Topology


namespace StatMech.Ising

noncomputable section

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]

@[simp] theorem coordinateAbs_apply
    (v : EuclideanSpace Real alpha) (i : alpha) :
    coordinateAbs v i = |v i| := rfl

theorem norm_coordinateAbs (v : EuclideanSpace Real alpha) :
    norm (coordinateAbs v) = norm v := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem matrix_inner_le_abs
    (A : Matrix alpha alpha Real) (hA : forall i j, 0 <= A i j)
    (v : EuclideanSpace Real alpha) :
    @inner Real _ _ (Matrix.toEuclideanLin A v) v <=
      @inner Real _ _ (Matrix.toEuclideanLin A (coordinateAbs v))
        (coordinateAbs v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, star_trivial, dotProduct,
    coordinateAbs, WithLp.ofLp_toLp]
  change (∑ i, v i * ∑ j, A i j * v j) <=
    ∑ i, |v i| * ∑ j, A i j * |v j|
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  calc
    v i * (A i j * v j) <= |v i * (A i j * v j)| := le_abs_self _
    _ = |v i| * (A i j * |v j|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hA i j)]


end
end StatMech.Ising
