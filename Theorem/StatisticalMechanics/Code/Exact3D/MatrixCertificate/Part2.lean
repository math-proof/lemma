/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part2


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem matrixVectorMul_memR_matVec {m n : ℕ} {A : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ} {I : IntervalMatrix m n} {X : IntervalVector n}
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i) (matrixVectorMul I X) := by
  simpa [matVec] using matrixVectorMul_memR hA hx


theorem matrixVectorMulNonneg_memR_matVec {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i) (matrixVectorMulNonneg I X hI hX) := by
  simpa [matVec] using matrixVectorMulNonneg_memR hI hX hA hx


theorem matrixVectorResidual_memR_matVec {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix n n} {X : IntervalVector n}
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i - x i) (matrixVectorResidual I X) := by
  simpa [matVec] using matrixVectorResidual_memR hA hx


theorem matrixVectorResidual_memR_matVec_pointVector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (center : Fin n → ℚ) :
    VectorMem
      (fun i => matVec A (fun j => (center j : ℝ)) i - (center i : ℝ))
      (matrixVectorResidual I (pointVector center)) :=
  matrixVectorResidual_memR_matVec hA (pointVector_memR center)


theorem matrixVectorResidualNonneg_memR_matVec {n : ℕ}
    {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix n n} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i - x i)
      (matrixVectorResidualNonneg I X hI hX) := by
  simpa [matVec] using matrixVectorResidualNonneg_memR hI hX hA hx


theorem matrixVectorResidualNonneg_memR_matVec_pointVector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hI : MatrixNonnegative I) (hA : MatrixMem A I)
    (center : Fin n → ℚ) (hcenter : ∀ i, 0 ≤ center i) :
    VectorMem
      (fun i => matVec A (fun j => (center j : ℝ)) i - (center i : ℝ))
      (matrixVectorResidualNonneg I (pointVector center) hI
        (pointVector_nonnegative hcenter)) :=
  matrixVectorResidualNonneg_memR_matVec hI
    (pointVector_nonnegative hcenter) hA (pointVector_memR center)


theorem matrixVectorAffine_memR_affineMap {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => affineMap A b x i) (matrixVectorAffine I B X) := by
  simpa [affineMap, matVec] using matrixVectorAffine_memR hA hb hx


theorem matrixVectorAffineNonneg_memR_affineMap {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => affineMap A b x i)
      (matrixVectorAffineNonneg I B X hI hX) := by
  simpa [affineMap, matVec] using
    matrixVectorAffineNonneg_memR hI hX hA hb hx


theorem matrixVectorAffineResidual_memR_affineMap {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => affineMap A b x i - x i)
      (matrixVectorAffineResidual I B X) := by
  simpa [affineMap, matVec] using matrixVectorAffineResidual_memR hA hb hx


theorem matrixVectorAffineResidual_memR_affineMap_pointVector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ}
    {I : IntervalMatrix n n} {B : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B)
    (center : Fin n → ℚ) :
    VectorMem
      (fun i =>
        affineMap A b (fun j => (center j : ℝ)) i - (center i : ℝ))
      (matrixVectorAffineResidual I B (pointVector center)) :=
  matrixVectorAffineResidual_memR_affineMap hA hb
    (pointVector_memR center)


theorem matrixVectorAffineResidualNonneg_memR_affineMap {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => affineMap A b x i - x i)
      (matrixVectorAffineResidualNonneg I B X hI hX) := by
  simpa [affineMap, matVec] using
    matrixVectorAffineResidualNonneg_memR hI hX hA hb hx


theorem matrixVectorAffineResidualNonneg_memR_affineMap_pointVector {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ}
    {I : IntervalMatrix n n} {B : IntervalVector n}
    (hI : MatrixNonnegative I) (hA : MatrixMem A I)
    (hb : VectorMem b B) (center : Fin n → ℚ)
    (hcenter : ∀ i, 0 ≤ center i) :
    VectorMem
      (fun i =>
        affineMap A b (fun j => (center j : ℝ)) i - (center i : ℝ))
      (matrixVectorAffineResidualNonneg I B (pointVector center) hI
        (pointVector_nonnegative hcenter)) :=
  matrixVectorAffineResidualNonneg_memR_affineMap hI
    (pointVector_nonnegative hcenter) hA hb (pointVector_memR center)


theorem matrixVectorAffine_memR_matVec {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i + b i) (matrixVectorAffine I B X) := by
  simpa [affineMap] using matrixVectorAffine_memR_affineMap hA hb hx


theorem matrixVectorAffineNonneg_memR_matVec {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    {I : IntervalMatrix m n} {B : IntervalVector m} {X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i + b i)
      (matrixVectorAffineNonneg I B X hI hX) := by
  simpa [affineMap] using
    matrixVectorAffineNonneg_memR_affineMap hI hX hA hb hx


theorem matrixVectorAffineResidual_memR_matVec {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i + b i - x i)
      (matrixVectorAffineResidual I B X) := by
  simpa [affineMap] using matrixVectorAffineResidual_memR_affineMap hA hb hx


theorem matrixVectorAffineResidualNonneg_memR_matVec {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x : Fin n → ℝ}
    {I : IntervalMatrix n n} {B X : IntervalVector n}
    (hI : MatrixNonnegative I) (hX : VectorNonnegative X)
    (hA : MatrixMem A I) (hb : VectorMem b B) (hx : VectorMem x X) :
    VectorMem (fun i => matVec A x i + b i - x i)
      (matrixVectorAffineResidualNonneg I B X hI hX) := by
  simpa [affineMap] using
    matrixVectorAffineResidualNonneg_memR_affineMap hI hX hA hb hx


end RatInterval
end Exact3D
end StatMech
