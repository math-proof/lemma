/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
open MeasureTheory


namespace StatMech

namespace ConfigSpace

variable {E : Type*} {G : Type*}

section Group

variable [Group G] [MulAction G E]


def shift (g : G) (ω : ConfigSpace E) : ConfigSpace E := fun e => ω (g⁻¹ • e)

end Group
end ConfigSpace
end StatMech
