/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part3


namespace StatMech

namespace Exact3D

namespace RatInterval

def IntervalGershgorinRowDisk {n : ℕ}
    (I : IntervalMatrix n n) (lam : ℝ) (i : Fin n) : Prop :=
  ∃ a : ℝ, (I i i).MemR a ∧
    |lam - a| ≤ (IntervalOffDiagAbsRowSum I i : ℝ)


noncomputable def IntervalGershgorinRowInterval {n : ℕ}
    (I : IntervalMatrix n n) (i : Fin n) : RatInterval where
  lower := (I i i).lower - IntervalOffDiagAbsRowSum I i
  upper := (I i i).upper + IntervalOffDiagAbsRowSum I i
  lower_le_upper := by
    have hdiag := (I i i).lower_le_upper
    have hradius := IntervalOffDiagAbsRowSum_nonneg I i
    linarith


end RatInterval
end Exact3D
end StatMech
