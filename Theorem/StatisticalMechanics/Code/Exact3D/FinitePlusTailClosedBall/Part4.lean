/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4


namespace StatMech

namespace Exact3D

open scoped NNReal


namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}


@[simp] theorem with_larger_radius_contraction
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).contraction = C.contraction :=
  rfl

@[simp] theorem with_larger_radius_center
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).center = C.center :=
  rfl

@[simp] theorem with_larger_radius_radius
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).radius = radius' :=
  rfl

@[simp] theorem with_larger_radius_residual
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).residual = C.residual :=
  rfl


@[simp] theorem with_larger_radius_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).fixedPoint = C.fixedPoint :=
  rfl


theorem mapsClosedBall_of_radius_le
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    FinitePlusTailState.MapsClosedBall
      C.contraction.map C.center radius' := by
  simpa using (C.with_larger_radius hradius).mapsClosedBall


theorem exists_fixedPoint_of_radius_le
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    ∃ p : FinitePlusTailState n α,
      C.contraction.map p = p ∧
        FinitePlusTailState.ClosedBall C.center radius' p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed,
    C.fixedPoint_mem_of_radius_le hradius⟩


theorem iterate_mem_of_radius_le
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    {x : FinitePlusTailState n α}
    (hx : FinitePlusTailState.ClosedBall C.center radius' x) (k : ℕ) :
    FinitePlusTailState.ClosedBall C.center radius'
      (C.contraction.iterate k x) := by
  simpa using (C.with_larger_radius hradius).iterate_mem hx k

end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
