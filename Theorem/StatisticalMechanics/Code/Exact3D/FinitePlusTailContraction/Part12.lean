/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part9
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


theorem iterate_contracts
    (C : FinitePlusTailLipschitzCertificate n α) (k : ℕ)
    (x y : FinitePlusTailState n α) :
    (C.iterate k x).dist (C.iterate k y) ≤ C.c ^ k * x.dist y := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      calc
        (C.iterate (k + 1) x).dist (C.iterate (k + 1) y) =
            (C.map (C.iterate k x)).dist (C.map (C.iterate k y)) := rfl
        _ ≤ C.c * (C.iterate k x).dist (C.iterate k y) :=
          C.mixed_lipschitz _ _
        _ ≤ C.c * (C.c ^ k * x.dist y) := by
          exact mul_le_mul_of_nonneg_left ih C.c_nonneg
        _ = C.c ^ (k + 1) * x.dist y := by
          ring


theorem mapsClosedBall_iterate_mem
    (C : FinitePlusTailLipschitzCertificate n α)
    {center : FinitePlusTailState n α} {radius : ℝ}
    (hmap : FinitePlusTailState.MapsClosedBall C.map center radius)
    {x : FinitePlusTailState n α}
    (hx : FinitePlusTailState.ClosedBall center radius x) (k : ℕ) :
    FinitePlusTailState.ClosedBall center radius (C.iterate k x) := by
  induction k with
  | zero =>
      simpa [iterate] using hx
  | succ _ ih =>
      exact hmap _ ih


theorem mapsClosedBall_of_residual_and_lipschitz
    (C : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hresidual : (C.map center).dist center ≤ residual)
    (hradius : residual + C.c * radius ≤ radius) :
    FinitePlusTailState.MapsClosedBall C.map center radius := by
  intro x hx
  unfold FinitePlusTailState.ClosedBall at hx ⊢
  calc
    (C.map x).dist center ≤
        (C.map x).dist (C.map center) + (C.map center).dist center :=
      FinitePlusTailState.dist_triangle (C.map x) (C.map center) center
    _ ≤ C.c * x.dist center + residual := by
      exact add_le_add (C.mixed_lipschitz x center) hresidual
    _ ≤ C.c * radius + residual := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hx C.c_nonneg) residual
    _ = residual + C.c * radius := by
      ring
    _ ≤ radius := hradius


theorem contractingWith
    (C : FinitePlusTailLipschitzCertificate n α) :
    ContractingWith (⟨C.c, C.c_nonneg⟩ : NNReal) C.map := by
  constructor
  · exact_mod_cast C.c_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    change (C.map x).dist (C.map y) ≤ C.c * x.dist y
    exact C.mixed_lipschitz x y


end FinitePlusTailLipschitzCertificate
end Exact3D
end StatMech
