/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part14


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplittingExample

theorem splittingFromRowSum_certificate_cone_iterate {η : ℝ} (hη : 0 ≤ η)
    {x : (splittingFromRowSum.certificate scale model).H.carrier}
    (hx : splittingFromRowSum.cone η x) (k : ℕ) :
    splittingFromRowSum.cone η
      ((((splittingFromRowSum.certificate scale model).R.map)^[k]) x) :=
  splittingFromRowSum.certificate_cone_iterate scale model hη hx k


theorem certificate_fixedPointEnclosure :
    certificate.FixedPointEnclosure :=
  splitting.certificate_fixedPointEnclosure scale model

end FiniteHyperbolicSplittingExample
end Exact3D
end StatMech
