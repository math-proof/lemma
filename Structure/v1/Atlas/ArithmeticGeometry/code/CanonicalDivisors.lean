/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CanonicalDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors


namespace PicardGroup

section DegreeMap

variable {Div : Type*} [AddCommGroup Div]

variable {PrincDiv : AddSubgroup Div}

variable (deg : Div →+ ℤ)

variable (hdeg : PrincDiv ≤ deg.ker)

omit [AddCommGroup Div] in

structure IsDivOmegaMaximal [PartialOrder Div] (ω : Ω) : Prop where
  mem : omegaD ω (divΩ ω)
  le_divΩ : ∀ D : Div, omegaD ω D → D ≤ divΩ ω

end DegreeMap
end PicardGroup
