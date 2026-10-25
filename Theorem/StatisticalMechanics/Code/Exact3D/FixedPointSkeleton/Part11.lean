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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part11


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace ClosedBallContractionCertificate

variable {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ}


@[simp] theorem with_larger_radius_fixedPoint
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).fixedPoint = C.fixedPoint :=
  rfl


theorem fixedPoint_isFixed (C : ClosedBallContractionCertificate F) :
    F C.fixedPoint = C.fixedPoint :=
  certifiedFixedPointOfL1Contraction_isFixed F C.c_nonneg C.c_lt_one
    C.lipschitz


theorem fixedPoint_unique (C : ClosedBallContractionCertificate F)
    {x y : Fin n → ℝ} (hx : F x = x) (hy : F y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction F C.c_lt_one C.lipschitz hx hy


theorem fixedPoint_mem (C : ClosedBallContractionCertificate F)
    {x : Fin n → ℝ} (hx : F x = x) :
    ClosedBall C.center C.radius x := by
  unfold ClosedBall
  have hd :
      l1Dist x C.center ≤
        C.c * l1Dist x C.center + (1 - C.c) * C.radius := by
    calc
      l1Dist x C.center = l1Dist (F x) C.center := by rw [hx]
      _ ≤ l1Dist (F x) (F C.center) + l1Dist (F C.center) C.center :=
        l1Dist_triangle (F x) (F C.center) C.center
      _ ≤ C.c * l1Dist x C.center + (1 - C.c) * C.radius := by
        exact add_le_add (C.lipschitz x C.center) C.residual_bound
  nlinarith [hd, C.c_lt_one]


theorem fixedPoint_mem_selected (C : ClosedBallContractionCertificate F) :
    ClosedBall C.center C.radius C.fixedPoint :=
  C.fixedPoint_mem C.fixedPoint_isFixed


theorem fixedPoint_mem_of_radius_le
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    ClosedBall C.center radius' C.fixedPoint :=
  closedBall_mono_radius C.fixedPoint_mem_selected hradius


theorem exists_fixedPoint (C : ClosedBallContractionCertificate F) :
    ∃ p : Fin n → ℝ, F p = p ∧ ClosedBall C.center C.radius p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed, C.fixedPoint_mem_selected⟩


theorem exists_unique_fixedPoint (C : ClosedBallContractionCertificate F) :
    ∃! p : Fin n → ℝ, F p = p := by
  refine ⟨C.fixedPoint, C.fixedPoint_isFixed, ?_⟩
  intro y hy
  exact C.fixedPoint_unique hy C.fixedPoint_isFixed


theorem eq_fixedPoint_of_isFixed (C : ClosedBallContractionCertificate F)
    {x : Fin n → ℝ} (hx : F x = x) : x = C.fixedPoint :=
  C.fixedPoint_unique hx C.fixedPoint_isFixed


theorem iterate_mem (C : ClosedBallContractionCertificate F)
    {x : Fin n → ℝ} (hx : ClosedBall C.center C.radius x) (k : ℕ) :
    ClosedBall C.center C.radius (FiniteContraction.iterate F k x) :=
  mapsClosedBall_iterate_mem C.mapsClosedBall hx k


theorem iterate_mem_of_radius_le
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') {x : Fin n → ℝ}
    (hx : ClosedBall C.center radius' x) (k : ℕ) :
    ClosedBall C.center radius' (FiniteContraction.iterate F k x) :=
  (C.with_larger_radius hradius).iterate_mem hx k


theorem iterate_l1Dist_le_pow_mul_of_fixed
    (C : ClosedBallContractionCertificate F)
    {p : Fin n → ℝ} (hp : F p = p) (x : Fin n → ℝ) (k : ℕ) :
    l1Dist (FiniteContraction.iterate F k x) p ≤ C.c ^ k * l1Dist x p :=
  FiniteContraction.iterate_l1Dist_le_pow_mul_of_fixed C.c_nonneg C.lipschitz
    hp x k


theorem iterate_l1Dist_le_pow_mul_fixedPoint
    (C : ClosedBallContractionCertificate F) (x : Fin n → ℝ) (k : ℕ) :
    l1Dist (FiniteContraction.iterate F k x) C.fixedPoint ≤
      C.c ^ k * l1Dist x C.fixedPoint :=
  C.iterate_l1Dist_le_pow_mul_of_fixed C.fixedPoint_isFixed x k

end ClosedBallContractionCertificate


theorem matVec_fixedPoint_unique_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    {x y : Fin n → ℝ}
    (hx : (fun x i => RatInterval.matVec A x i) x = x)
    (hy : (fun x i => RatInterval.matVec A x i) y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction
    (fun x i => RatInterval.matVec A x i) hcontract
    (lipschitz_matVec_of_rowSumContraction hI hA) hx hy


theorem matVec_fixedPoint_unique_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    {x y : Fin n → ℝ}
    (hx : (fun x i => RatInterval.matVec A x i) x = x)
    (hy : (fun x i => RatInterval.matVec A x i) y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction
    (fun x i => RatInterval.matVec A x i) hI.constant_lt_one
    (lipschitz_matVec_of_columnSumContraction hI hA) hx hy


theorem affineMap_fixedPoint_unique_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    {x y : Fin n → ℝ}
    (hx : (fun x i => RatInterval.affineMap A b x i) x = x)
    (hy : (fun x i => RatInterval.affineMap A b x i) y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction
    (fun x i => RatInterval.affineMap A b x i) hcontract
    (lipschitz_affineMap_of_rowSumContraction hI hA b) hx hy


theorem affineMap_fixedPoint_unique_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) {x y : Fin n → ℝ}
    (hx : (fun x i => RatInterval.affineMap A b x i) x = x)
    (hy : (fun x i => RatInterval.affineMap A b x i) y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction
    (fun x i => RatInterval.affineMap A b x i) hI.constant_lt_one
    (lipschitz_affineMap_of_columnSumContraction hI hA b) hx hy


end FiniteContraction
end Exact3D
end StatMech
