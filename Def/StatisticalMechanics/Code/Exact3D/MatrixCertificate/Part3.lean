/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part2


namespace StatMech

namespace Exact3D

namespace RatInterval

noncomputable def offDiagAbsRowSum {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, if j = i then 0 else |A i j|


noncomputable def IntervalOffDiagAbsRowSum {n : ℕ}
    (I : IntervalMatrix n n) (i : Fin n) : ℚ :=
  ∑ j, if j = i then 0 else (I i j).absUpper


end RatInterval
end Exact3D
end StatMech
