/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace PicardGroup

section PicardGroupDef

variable (Div : Type*) [AddCommGroup Div]

variable (PrincDiv : AddSubgroup Div)

abbrev PicGrp := Div ⧸ PrincDiv

end PicardGroupDef
end PicardGroup
