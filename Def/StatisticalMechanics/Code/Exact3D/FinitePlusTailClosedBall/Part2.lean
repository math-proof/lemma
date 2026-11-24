module
public import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open scoped NNReal


namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}


noncomputable def fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState n α :=
  C.contraction.fixedPoint


end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
