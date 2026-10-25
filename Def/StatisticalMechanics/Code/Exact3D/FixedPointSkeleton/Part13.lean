/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part12


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

def closedBallContractionCertificate_of_rowSumContraction_and_residualVector
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℝ) {radius : ℝ} {R : RatInterval.IntervalVector n}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualMem : RatInterval.VectorMem
      (fun i => RatInterval.matVec A center i - center i) R)
    (hresidualSum :
      (RatInterval.VectorAbsSum R : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_rowSumContraction hI hA center hcontract
    hradius
    (le_trans (residual_l1Dist_le_of_vectorMem hresidualMem) hresidualSum)


def closedBallContractionCertificate_of_columnSumContraction_and_residualVector
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℝ) {radius : ℝ} {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hresidualMem : RatInterval.VectorMem
      (fun i => RatInterval.matVec A center i - center i) R)
    (hresidualSum :
      (RatInterval.VectorAbsSum R : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_columnSumContraction hI hA center
    hradius
    (le_trans (residual_l1Dist_le_of_vectorMem hresidualMem) hresidualSum)


def closedBallContractionCertificate_of_rowSumContraction_affine_and_residualVector
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b center : Fin n → ℝ) {radius : ℝ} {R : RatInterval.IntervalVector n}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualMem : RatInterval.VectorMem
      (fun i => RatInterval.affineMap A b center i - center i) R)
    (hresidualSum :
      (RatInterval.VectorAbsSum R : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_rowSumContraction_affine hI hA b center
    hcontract hradius
    (le_trans (residual_l1Dist_le_of_vectorMem hresidualMem) hresidualSum)


def closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b center : Fin n → ℝ) {radius : ℝ} {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hresidualMem : RatInterval.VectorMem
      (fun i => RatInterval.affineMap A b center i - center i) R)
    (hresidualSum :
      (RatInterval.VectorAbsSum R : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine hI hA b center
    hradius
    (le_trans (residual_l1Dist_le_of_vectorMem hresidualMem) hresidualSum)


def closedBallContractionCertificate_of_rowSumContraction_and_rationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℚ) {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorResidual I (RatInterval.pointVector center)) :
          ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_rowSumContraction_and_residualVector
    hI hA (fun i => (center i : ℝ)) hcontract hradius
    (RatInterval.matrixVectorResidual_memR_matVec hA
      (RatInterval.pointVector_memR center))
    hresidualSum


def closedBallContractionCertificate_of_columnSumContraction_and_rationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℚ) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorResidual I (RatInterval.pointVector center)) :
          ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_columnSumContraction_and_residualVector
    hI hA (fun i => (center i : ℝ)) hradius
    (RatInterval.matrixVectorResidual_memR_matVec hA
      (RatInterval.pointVector_memR center))
    hresidualSum


def closedBallContractionCertificate_of_rowSumContraction_affine_and_rationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    {B : RatInterval.IntervalVector n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    {b : Fin n → ℝ} (hb : RatInterval.VectorMem b B)
    (center : Fin n → ℚ) {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorAffineResidual I B
          (RatInterval.pointVector center)) : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_rowSumContraction_affine_and_residualVector
    hI hA b (fun i => (center i : ℝ)) hcontract hradius
    (RatInterval.matrixVectorAffineResidual_memR_affineMap hA hb
      (RatInterval.pointVector_memR center))
    hresidualSum


def closedBallContractionCertificate_of_columnSumContraction_affine_and_rationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    {B : RatInterval.IntervalVector n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    {b : Fin n → ℝ} (hb : RatInterval.VectorMem b B)
    (center : Fin n → ℚ) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorAffineResidual I B
          (RatInterval.pointVector center)) : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector
    hI hA b (fun i => (center i : ℝ)) hradius
    (RatInterval.matrixVectorAffineResidual_memR_affineMap hA hb
      (RatInterval.pointVector_memR center))
    hresidualSum


def closedBallContractionCertificate_of_rowSumContraction_and_nonnegRationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hI_nonneg : RatInterval.MatrixNonnegative I)
    (center : Fin n → ℚ) (hcenter_nonneg : ∀ i, 0 ≤ center i)
    {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorResidualNonneg I
          (RatInterval.pointVector center) hI_nonneg
          (RatInterval.pointVector_nonnegative hcenter_nonneg)) : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_rowSumContraction_and_residualVector
    hI hA (fun i => (center i : ℝ)) hcontract hradius
    (RatInterval.matrixVectorResidualNonneg_memR_matVec_pointVector
      hI_nonneg hA center hcenter_nonneg)
    hresidualSum


def closedBallContractionCertificate_of_columnSumContraction_and_nonnegRationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hI_nonneg : RatInterval.MatrixNonnegative I)
    (center : Fin n → ℚ) (hcenter_nonneg : ∀ i, 0 ≤ center i)
    {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorResidualNonneg I
          (RatInterval.pointVector center) hI_nonneg
          (RatInterval.pointVector_nonnegative hcenter_nonneg)) : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_columnSumContraction_and_residualVector
    hI hA (fun i => (center i : ℝ)) hradius
    (RatInterval.matrixVectorResidualNonneg_memR_matVec_pointVector
      hI_nonneg hA center hcenter_nonneg)
    hresidualSum


def closedBallContractionCertificate_of_rowSumContraction_affine_and_nonnegRationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    {B : RatInterval.IntervalVector n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hI_nonneg : RatInterval.MatrixNonnegative I)
    {b : Fin n → ℝ} (hb : RatInterval.VectorMem b B)
    (center : Fin n → ℚ) (hcenter_nonneg : ∀ i, 0 ≤ center i)
    {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorAffineResidualNonneg I B
          (RatInterval.pointVector center) hI_nonneg
          (RatInterval.pointVector_nonnegative hcenter_nonneg)) : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_rowSumContraction_affine_and_residualVector
    hI hA b (fun i => (center i : ℝ)) hcontract hradius
    (RatInterval.matrixVectorAffineResidualNonneg_memR_affineMap_pointVector
      hI_nonneg hA hb center hcenter_nonneg)
    hresidualSum


def closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    {B : RatInterval.IntervalVector n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hI_nonneg : RatInterval.MatrixNonnegative I)
    {b : Fin n → ℝ} (hb : RatInterval.VectorMem b B)
    (center : Fin n → ℚ) (hcenter_nonneg : ∀ i, 0 ≤ center i)
    {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorAffineResidualNonneg I B
          (RatInterval.pointVector center) hI_nonneg
          (RatInterval.pointVector_nonnegative hcenter_nonneg)) : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector
    hI hA b (fun i => (center i : ℝ)) hradius
    (RatInterval.matrixVectorAffineResidualNonneg_memR_affineMap
      hI_nonneg (RatInterval.pointVector_nonnegative hcenter_nonneg) hA hb
      (RatInterval.pointVector_memR center))
    hresidualSum


def zeroMap {n : ℕ} (_x : Fin n → ℝ) (_i : Fin n) : ℝ :=
  0


end FiniteContraction
end Exact3D
end StatMech
