/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG


namespace StatMech

namespace Exact3D

namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type}


@[simp] theorem rgMap_map
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) :
    (C.rgMap scale).map = C.contraction.map :=
  rfl


@[simp] theorem rgMap_scale
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) :
    (C.rgMap scale).scale = scale :=
  rfl


end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
