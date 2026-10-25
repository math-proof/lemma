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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part11


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

def closedBallContractionCertificate_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℝ) {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidual :
      l1Dist ((fun x i => RatInterval.matVec A x i) center) center ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) where
  center := center
  radius := radius
  c := (n : ℝ) * (hI.c : ℝ)
  c_nonneg := by
    exact mul_nonneg (Nat.cast_nonneg n) (by exact_mod_cast hI.c_nonneg)
  c_lt_one := hcontract
  radius_nonneg := hradius
  lipschitz := lipschitz_matVec_of_rowSumContraction hI hA
  residual_bound := hresidual


def closedBallContractionCertificate_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℝ) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual :
      l1Dist ((fun x i => RatInterval.matVec A x i) center) center ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) where
  center := center
  radius := radius
  c := hI.c
  c_nonneg := by exact_mod_cast hI.c_nonneg
  c_lt_one := hI.constant_lt_one
  radius_nonneg := hradius
  lipschitz := lipschitz_matVec_of_columnSumContraction hI hA
  residual_bound := hresidual


def closedBallContractionCertificate_of_rowSumContraction_affine {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b center : Fin n → ℝ) {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidual :
      l1Dist ((fun x i => RatInterval.affineMap A b x i) center) center ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) where
  center := center
  radius := radius
  c := (n : ℝ) * (hI.c : ℝ)
  c_nonneg := by
    exact mul_nonneg (Nat.cast_nonneg n) (by exact_mod_cast hI.c_nonneg)
  c_lt_one := hcontract
  radius_nonneg := hradius
  lipschitz := lipschitz_affineMap_of_rowSumContraction hI hA b
  residual_bound := hresidual


def closedBallContractionCertificate_of_columnSumContraction_affine {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b center : Fin n → ℝ) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual :
      l1Dist ((fun x i => RatInterval.affineMap A b x i) center) center ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) where
  center := center
  radius := radius
  c := hI.c
  c_nonneg := by exact_mod_cast hI.c_nonneg
  c_lt_one := hI.constant_lt_one
  radius_nonneg := hradius
  lipschitz := lipschitz_affineMap_of_columnSumContraction hI hA b
  residual_bound := hresidual


end FiniteContraction
end Exact3D
end StatMech
