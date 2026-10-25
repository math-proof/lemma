/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Abbrev.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG


namespace StatMech

namespace Exact3D

namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type}


noncomputable def rgMap
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) : BlockSpinMap C.hamiltonian where
  scale := scale
  map := C.contraction.map

end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
