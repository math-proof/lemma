/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
/-- Decomposition of a tempered distribution `u` away from a closed conic set `Γ` disjoint from the
conic singular support: `u` can be written as `u₁' + u₁'' + u₂` where `u₁'` is compactly supported,
`u₁''` vanishes on test functions supported far from the origin and supported in directions in `Γ`,
`u₂` is Schwartz, and the conic support of `u₁' + u₁''` is disjoint from `Γ`. -/


namespace ConeSupport

variable {n : ℕ}


end ConeSupport

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory

end
