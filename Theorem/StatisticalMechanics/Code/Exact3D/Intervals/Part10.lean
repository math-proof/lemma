/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part11


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem MatrixMem.row_sum_le {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {I : IntervalMatrix m n} (hA : MatrixMem A I) (i : Fin m) :
    (∑ j, A i j) ≤ (MatrixUpperRowSum I i : ℝ) := by
  calc
    (∑ j, A i j) ≤ ∑ j, ((I i j).upper : ℝ) := by
      exact Finset.sum_le_sum fun j _ => (hA i j).2
    _ = (MatrixUpperRowSum I i : ℝ) := by
      simp [MatrixUpperRowSum]


theorem MatrixMem.row_abs_sum_le {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {I : IntervalMatrix m n} (hA : MatrixMem A I) (i : Fin m) :
    (∑ j, |A i j|) ≤ (MatrixAbsRowSum I i : ℝ) := by
  calc
    (∑ j, |A i j|) ≤ ∑ j, ((I i j).absUpper : ℝ) := by
      exact Finset.sum_le_sum fun j _ => abs_le_absUpper_of_memR (hA i j)
    _ = (MatrixAbsRowSum I i : ℝ) := by
      simp [MatrixAbsRowSum]


theorem MatrixMem.col_abs_sum_le {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {I : IntervalMatrix m n} (hA : MatrixMem A I) (j : Fin n) :
    (∑ i, |A i j|) ≤ (MatrixAbsColSum I j : ℝ) := by
  calc
    (∑ i, |A i j|) ≤ ∑ i, ((I i j).absUpper : ℝ) := by
      exact Finset.sum_le_sum fun i _ => abs_le_absUpper_of_memR (hA i j)
    _ = (MatrixAbsColSum I j : ℝ) := by
      simp [MatrixAbsColSum]


theorem VectorMem.abs_sum_le {n : ℕ} {x : Fin n → ℝ} {I : IntervalVector n}
    (hx : VectorMem x I) :
    (∑ i, |x i|) ≤ (VectorAbsSum I : ℝ) := by
  calc
    (∑ i, |x i|) ≤ ∑ i, ((I i).absUpper : ℝ) := by
      exact Finset.sum_le_sum fun i _ => abs_le_absUpper_of_memR (hx i)
    _ = (VectorAbsSum I : ℝ) := by
      simp [VectorAbsSum]


theorem vectorAdd_memR {n : ℕ} {x y : Fin n → ℝ}
    {I J : IntervalVector n} (hx : VectorMem x I) (hy : VectorMem y J) :
    VectorMem (fun i => x i + y i) (vectorAdd I J) := by
  intro i
  exact add_memR (hx i) (hy i)


theorem vectorNeg_memR {n : ℕ} {x : Fin n → ℝ} {I : IntervalVector n}
    (hx : VectorMem x I) :
    VectorMem (fun i => -x i) (vectorNeg I) := by
  intro i
  exact neg_memR (hx i)


theorem vectorSub_memR {n : ℕ} {x y : Fin n → ℝ}
    {I J : IntervalVector n} (hx : VectorMem x I) (hy : VectorMem y J) :
    VectorMem (fun i => x i - y i) (vectorSub I J) := by
  intro i
  exact sub_memR (hx i) (hy i)


theorem vectorAdd_memQ {n : ℕ} {x y : Fin n → ℚ}
    {I J : IntervalVector n} (hx : VectorMemQ x I) (hy : VectorMemQ y J) :
    VectorMemQ (fun i => x i + y i) (vectorAdd I J) := by
  intro i
  exact add_memQ (hx i) (hy i)


theorem vectorNeg_memQ {n : ℕ} {x : Fin n → ℚ} {I : IntervalVector n}
    (hx : VectorMemQ x I) :
    VectorMemQ (fun i => -x i) (vectorNeg I) := by
  intro i
  exact neg_memQ (hx i)


theorem vectorSub_memQ {n : ℕ} {x y : Fin n → ℚ}
    {I J : IntervalVector n} (hx : VectorMemQ x I) (hy : VectorMemQ y J) :
    VectorMemQ (fun i => x i - y i) (vectorSub I J) := by
  intro i
  exact sub_memQ (hx i) (hy i)


theorem pointVector_memQ {n : ℕ} (x : Fin n → ℚ) :
    VectorMemQ x (pointVector x) := by
  intro i
  exact point_memQ (x i)


theorem pointVector_memR {n : ℕ} (x : Fin n → ℚ) :
    VectorMem (fun i => (x i : ℝ)) (pointVector x) := by
  exact (pointVector_memQ x).memR_coe


theorem pointMatrix_memQ {m n : ℕ} (A : Fin m → Fin n → ℚ) :
    MatrixMemQ A (pointMatrix A) := by
  intro i j
  exact point_memQ (A i j)


theorem pointMatrix_memR {m n : ℕ} (A : Fin m → Fin n → ℚ) :
    MatrixMem (fun i j => (A i j : ℝ)) (pointMatrix A) :=
  (pointMatrix_memQ A).memR_coe


theorem matrixVectorMul_memR {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ} {I : IntervalMatrix m n} {X : IntervalVector n}
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => ∑ j, A i j * x j) (matrixVectorMul I X) := by
  intro i
  unfold matrixVectorMul
  simpa using finsetSum_memR (s := Finset.univ)
    (I := fun j => mul (I i j) (X j))
    (x := fun j => A i j * x j)
    (fun j _ => mul_memR (hA i j) (hx j))


theorem matrixVectorMulNonneg_memR {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => ∑ j, A i j * x j)
      (matrixVectorMulNonneg I X hI hX) := by
  intro i
  unfold matrixVectorMulNonneg
  simpa using finsetSum_memR (s := Finset.univ)
    (I := fun j => mulNonneg (I i j) (X j) (hI i j) (hX j))
    (x := fun j => A i j * x j)
    (fun j _ => mulNonneg_memR (hI i j) (hX j) (hA i j) (hx j))


theorem matrixVectorResidual_memR {n : ℕ} {A : Fin n → Fin n → ℝ}
    {x : Fin n → ℝ} {I : IntervalMatrix n n} {X : IntervalVector n}
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => (∑ j, A i j * x j) - x i)
      (matrixVectorResidual I X) := by
  exact vectorSub_memR (matrixVectorMul_memR hA hx) hx


theorem matrixVectorResidualNonneg_memR {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix n n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => (∑ j, A i j * x j) - x i)
      (matrixVectorResidualNonneg I X hI hX) := by
  exact vectorSub_memR (matrixVectorMulNonneg_memR hI hX hA hx) hx


theorem matrixVectorAffine_memR {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {b : Fin m → ℝ} {x : Fin n → ℝ} {I : IntervalMatrix m n}
    {B : IntervalVector m} {X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => (∑ j, A i j * x j) + b i)
      (matrixVectorAffine I B X) := by
  exact vectorAdd_memR (matrixVectorMul_memR hA hx) hb


theorem matrixVectorAffineNonneg_memR {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => (∑ j, A i j * x j) + b i)
      (matrixVectorAffineNonneg I B X hI hX) := by
  exact vectorAdd_memR (matrixVectorMulNonneg_memR hI hX hA hx) hb


theorem matrixVectorAffineResidual_memR {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => ((∑ j, A i j * x j) + b i) - x i)
      (matrixVectorAffineResidual I B X) := by
  exact vectorSub_memR (matrixVectorAffine_memR hA hb hx) hx


theorem matrixVectorAffineResidualNonneg_memR {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => ((∑ j, A i j * x j) + b i) - x i)
      (matrixVectorAffineResidualNonneg I B X hI hX) := by
  exact vectorSub_memR (matrixVectorAffineNonneg_memR hI hX hA hb hx) hx


theorem matrixVectorMulNonneg_nonnegative {m n : ℕ}
    {I : IntervalMatrix m n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X) :
    VectorNonnegative (matrixVectorMulNonneg I X hI hX) := by
  intro i
  unfold matrixVectorMulNonneg
  exact finsetSum_nonnegative fun j _ =>
    mulNonneg_nonnegative (hI i j) (hX j)


theorem matrixVectorAffineNonneg_nonnegative {m n : ℕ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hB : VectorNonnegative B)
    (hX : VectorNonnegative X) :
    VectorNonnegative (matrixVectorAffineNonneg I B X hI hX) :=
  vectorAdd_nonnegative (matrixVectorMulNonneg_nonnegative hI hX) hB


theorem matrixVectorMul_memQ {m n : ℕ} {A : Fin m → Fin n → ℚ}
    {x : Fin n → ℚ} {I : IntervalMatrix m n} {X : IntervalVector n}
    (hA : MatrixMemQ A I) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => ∑ j, A i j * x j) (matrixVectorMul I X) := by
  intro i
  unfold matrixVectorMul
  simpa using finsetSum_memQ (s := Finset.univ)
    (I := fun j => mul (I i j) (X j))
    (x := fun j => A i j * x j)
    (fun j _ => mul_memQ (hA i j) (hx j))


theorem matrixVectorMulNonneg_memQ {m n : ℕ}
    {A : Fin m → Fin n → ℚ} {x : Fin n → ℚ}
    {I : IntervalMatrix m n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMemQ A I) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => ∑ j, A i j * x j)
      (matrixVectorMulNonneg I X hI hX) := by
  intro i
  unfold matrixVectorMulNonneg
  simpa using finsetSum_memQ (s := Finset.univ)
    (I := fun j => mulNonneg (I i j) (X j) (hI i j) (hX j))
    (x := fun j => A i j * x j)
    (fun j _ => mulNonneg_memQ (hI i j) (hX j) (hA i j) (hx j))


theorem matrixVectorResidual_memQ {n : ℕ} {A : Fin n → Fin n → ℚ}
    {x : Fin n → ℚ} {I : IntervalMatrix n n} {X : IntervalVector n}
    (hA : MatrixMemQ A I) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => (∑ j, A i j * x j) - x i)
      (matrixVectorResidual I X) := by
  exact vectorSub_memQ (matrixVectorMul_memQ hA hx) hx


theorem matrixVectorResidualNonneg_memQ {n : ℕ}
    {A : Fin n → Fin n → ℚ} {x : Fin n → ℚ}
    {I : IntervalMatrix n n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMemQ A I) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => (∑ j, A i j * x j) - x i)
      (matrixVectorResidualNonneg I X hI hX) := by
  exact vectorSub_memQ (matrixVectorMulNonneg_memQ hI hX hA hx) hx


theorem matrixVectorAffine_memQ {m n : ℕ} {A : Fin m → Fin n → ℚ}
    {b : Fin m → ℚ} {x : Fin n → ℚ} {I : IntervalMatrix m n}
    {B : IntervalVector m} {X : IntervalVector n}
    (hA : MatrixMemQ A I) (hb : VectorMemQ b B) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => (∑ j, A i j * x j) + b i)
      (matrixVectorAffine I B X) := by
  exact vectorAdd_memQ (matrixVectorMul_memQ hA hx) hb


theorem matrixVectorAffineNonneg_memQ {m n : ℕ}
    {A : Fin m → Fin n → ℚ} {b : Fin m → ℚ} {x : Fin n → ℚ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMemQ A I) (hb : VectorMemQ b B) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => (∑ j, A i j * x j) + b i)
      (matrixVectorAffineNonneg I B X hI hX) := by
  exact vectorAdd_memQ (matrixVectorMulNonneg_memQ hI hX hA hx) hb


theorem matrixVectorAffineResidual_memQ {n : ℕ}
    {A : Fin n → Fin n → ℚ} {b x : Fin n → ℚ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hA : MatrixMemQ A I) (hb : VectorMemQ b B) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => ((∑ j, A i j * x j) + b i) - x i)
      (matrixVectorAffineResidual I B X) := by
  exact vectorSub_memQ (matrixVectorAffine_memQ hA hb hx) hx


theorem matrixVectorAffineResidualNonneg_memQ {n : ℕ}
    {A : Fin n → Fin n → ℚ} {b x : Fin n → ℚ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMemQ A I) (hb : VectorMemQ b B) (hx : VectorMemQ x X) :
    VectorMemQ (fun i => ((∑ j, A i j * x j) + b i) - x i)
      (matrixVectorAffineResidualNonneg I B X hI hX) := by
  exact vectorSub_memQ (matrixVectorAffineNonneg_memQ hI hX hA hb hx) hx


end RatInterval
end Exact3D
end StatMech
