/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear


namespace SerreDualityP1

open CohomologyP1


/-- The composition `residueShift ∘ residueShift` equals the identity. -/
theorem residueShift_comp_self : residueShift ∘ residueShift = id := by
  funext i; simp [residueShift]


end SerreDualityP1
