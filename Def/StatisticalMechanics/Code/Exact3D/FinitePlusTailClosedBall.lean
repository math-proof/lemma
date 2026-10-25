/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Structure.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall


namespace StatMech

namespace Exact3D

open scoped NNReal


namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}


def ofResidualBound
    (contraction : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (contraction.map center).dist center ≤ residual)
    (hbudget : residual + contraction.c * radius ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate n α where
  contraction := contraction
  center := center
  radius := radius
  residual := residual
  radius_nonneg := hradius
  residual_bound := hresidual
  radius_bound := hbudget


def ofResidualMargin
    (contraction : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual :
      (contraction.map center).dist center ≤
        (1 - contraction.c) * radius) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  ofResidualBound contraction center
    (radius := radius) (residual := (1 - contraction.c) * radius)
    hradius hresidual (by
      ring_nf
      exact le_rfl)


def ofFixedCenter
    (contraction : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hfixed : contraction.map center = center) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  ofResidualBound contraction center (radius := radius) (residual := 0)
    hradius
    (by rw [hfixed, FinitePlusTailState.dist_self])
    (by
      calc
        0 + contraction.c * radius ≤ 1 * radius := by
          simpa using
            mul_le_mul_of_nonneg_right contraction.c_lt_one.le hradius
      _ = radius := by ring)


noncomputable def ofFiniteClosedBall
    {finiteMap : (Fin n → ℝ) → Fin n → ℝ}
    (C : FiniteContraction.ClosedBallContractionCertificate finiteMap) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  ofResidualMargin
    (FinitePlusTailLipschitzCertificate.ofFiniteMap
      (α := α) finiteMap C.c_nonneg C.c_lt_one C.lipschitz)
    (FinitePlusTailState.ofFinite (α := α) C.center)
    C.radius_nonneg
    (by
      simpa using C.residual_bound)


end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
