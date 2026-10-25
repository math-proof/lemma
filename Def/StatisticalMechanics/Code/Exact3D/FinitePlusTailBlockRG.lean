/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
import Structure.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


noncomputable def stableCertificate
    (P : FinitePlusTailBlockRGPackage n α) :
    FinitePlusTailLipschitzCertificate n α :=
  P.blockBounds.toLipschitzCertificate
    P.c_nonneg P.c_lt_one
    P.finite_column_sum_le P.tail_column_sum_le

end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
