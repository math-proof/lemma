/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.Foundations.ConfigSpace
open MeasureTheory TopologicalSpace


namespace StatMech

namespace ConfigSpace

variable {E : Type*}


def eval (e : E) (ω : ConfigSpace E) : Bool := ω e

end ConfigSpace
end StatMech
