/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12


namespace StatMech

namespace Exact3D

open scoped NNReal


structure FinitePlusTailClosedBallContractionCertificate (n : ℕ) (α : Type*) where
  contraction : FinitePlusTailLipschitzCertificate n α
  center : FinitePlusTailState n α
  radius : ℝ
  residual : ℝ
  radius_nonneg : 0 ≤ radius
  residual_bound : (contraction.map center).dist center ≤ residual
  radius_bound : residual + contraction.c * radius ≤ radius

end Exact3D
end StatMech
