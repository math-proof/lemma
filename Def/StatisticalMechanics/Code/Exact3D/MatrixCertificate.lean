/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12


namespace StatMech

namespace Exact3D

namespace RatInterval

noncomputable def supNormVec {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, |x i|

end RatInterval
end Exact3D
end StatMech
