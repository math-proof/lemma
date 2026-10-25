/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part10


namespace StatMech

namespace Exact3D

namespace RatInterval

@[simp] theorem pointVector_apply {n : ℕ} (x : Fin n → ℚ) (i : Fin n) :
    pointVector x i = point (x i) :=
  rfl

@[simp] theorem pointMatrix_apply {m n : ℕ}
    (A : Fin m → Fin n → ℚ) (i : Fin m) (j : Fin n) :
    pointMatrix A i j = point (A i j) :=
  rfl


theorem pointVector_nonnegative {n : ℕ} {x : Fin n → ℚ}
    (hx : ∀ i, 0 ≤ x i) :
    VectorNonnegative (pointVector x) := by
  intro i
  exact point_nonnegative (hx i)


theorem pointMatrix_nonnegative {m n : ℕ} {A : Fin m → Fin n → ℚ}
    (hA : ∀ i j, 0 ≤ A i j) :
    MatrixNonnegative (pointMatrix A) := by
  intro i j
  exact point_nonnegative (hA i j)


theorem VectorAbsSum_pointVector {n : ℕ} (x : Fin n → ℚ) :
    VectorAbsSum (pointVector x) = ∑ i, |x i| := by
  unfold VectorAbsSum pointVector
  apply Finset.sum_congr rfl
  intro i _
  exact absUpper_point (x i)


theorem MatrixAbsRowSum_pointMatrix {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (i : Fin m) :
    MatrixAbsRowSum (pointMatrix A) i = ∑ j, |A i j| := by
  unfold MatrixAbsRowSum pointMatrix
  apply Finset.sum_congr rfl
  intro j _
  exact absUpper_point (A i j)


theorem MatrixAbsColSum_pointMatrix {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (j : Fin n) :
    MatrixAbsColSum (pointMatrix A) j = ∑ i, |A i j| := by
  unfold MatrixAbsColSum pointMatrix
  apply Finset.sum_congr rfl
  intro i _
  exact absUpper_point (A i j)


end RatInterval
end Exact3D
end StatMech
