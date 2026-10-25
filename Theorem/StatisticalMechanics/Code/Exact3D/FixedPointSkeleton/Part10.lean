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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part10


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace ClosedBallContractionCertificate

variable {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ}


@[simp] theorem with_larger_radius_center
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).center = C.center :=
  rfl

@[simp] theorem with_larger_radius_radius
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).radius = radius' :=
  rfl

@[simp] theorem with_larger_radius_c
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).c = C.c :=
  rfl

end ClosedBallContractionCertificate


theorem fixedPoint_unique_of_l1_contraction {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc : c < 1) (hLip : LipschitzWithConstant F c)
    {x y : Fin n → ℝ} (hx : F x = x) (hy : F y = y) : x = y := by
  have hd : l1Dist x y ≤ c * l1Dist x y := by
    simpa [hx, hy] using hLip x y
  have hnot_pos : ¬ 0 < l1Dist x y := by
    intro hpos
    have hstrict : c * l1Dist x y < l1Dist x y := by
      nlinarith
    linarith
  have hdist_zero : l1Dist x y = 0 := by
    exact le_antisymm (le_of_not_gt hnot_pos) (l1Dist_nonneg x y)
  exact eq_of_l1Dist_eq_zero hdist_zero


theorem iterate_eq_of_fixed {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ}
    {x : Fin n → ℝ} (hx : F x = x) (k : ℕ) :
    iterate F k x = x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ _ ih =>
      simp [iterate, ih, hx]


theorem iterate_l1Dist_le_pow_mul_of_fixed {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hLip : LipschitzWithConstant F c)
    {p : Fin n → ℝ} (hp : F p = p) (x : Fin n → ℝ) (k : ℕ) :
    l1Dist (iterate F k x) p ≤ c ^ k * l1Dist x p := by
  have hiter := lipschitz_iterate hc_nonneg hLip k x p
  simpa [iterate_eq_of_fixed hp k] using hiter

end FiniteContraction
end Exact3D
end StatMech
