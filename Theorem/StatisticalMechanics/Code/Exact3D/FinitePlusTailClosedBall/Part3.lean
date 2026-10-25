/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part3


namespace StatMech

namespace Exact3D

open scoped NNReal


namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}


@[simp] theorem with_larger_residual_contraction
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).contraction =
      C.contraction :=
  rfl

@[simp] theorem with_larger_residual_center
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).center = C.center :=
  rfl

@[simp] theorem with_larger_residual_radius
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).radius = C.radius :=
  rfl

@[simp] theorem with_larger_residual_residual
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).residual = residual' :=
  rfl

@[simp] theorem with_larger_residual_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).fixedPoint =
      C.fixedPoint :=
  rfl


end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
