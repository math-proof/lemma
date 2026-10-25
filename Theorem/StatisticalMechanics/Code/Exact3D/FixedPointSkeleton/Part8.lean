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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part8


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem mapsClosedBall_iterate_mem {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {center : Fin n → ℝ} {radius : ℝ}
    (hmap : MapsClosedBall F center radius) {x : Fin n → ℝ}
    (hx : ClosedBall center radius x) (k : ℕ) :
    ClosedBall center radius (iterate F k x) := by
  induction k with
  | zero =>
      simpa [iterate] using hx
  | succ _ ih =>
      exact hmap _ ih


theorem mapsClosedBall_of_residual_and_lipschitz {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c radius : ℝ}
    (center : Fin n → ℝ)
    (hc_nonneg : 0 ≤ c)
    (hLip : LipschitzWithConstant F c)
    (hresidual : l1Dist (F center) center ≤ (1 - c) * radius) :
    MapsClosedBall F center radius := by
  intro x hx
  unfold ClosedBall at hx ⊢
  calc
    l1Dist (F x) center ≤ l1Dist (F x) (F center) + l1Dist (F center) center :=
      l1Dist_triangle (F x) (F center) center
    _ ≤ c * l1Dist x center + (1 - c) * radius := by
      exact add_le_add (hLip x center) hresidual
    _ ≤ c * radius + (1 - c) * radius := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx hc_nonneg) le_rfl
    _ = radius := by ring


theorem center_mem_closedBall {n : ℕ} (center : Fin n → ℝ) {radius : ℝ}
    (hradius : 0 ≤ radius) : ClosedBall center radius center := by
  unfold ClosedBall
  simpa [l1Dist_self] using hradius


theorem closedBall_mono_radius {n : ℕ} {center x : Fin n → ℝ}
    {radius radius' : ℝ}
    (hx : ClosedBall center radius x) (hradius : radius ≤ radius') :
    ClosedBall center radius' x :=
  le_trans hx hradius


end FiniteContraction
end Exact3D
end StatMech
