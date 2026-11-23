/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1

@[expose] public section

namespace SerreDualityP1

open CohomologyP1


/-- The residue shift `i ↦ -1 - i` realizing the duality at the index level. -/
def residueShift : ℤ → ℤ := fun i => -1 - i

end SerreDualityP1
