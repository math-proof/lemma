/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Abbrev.StatisticalMechanics.Code.Foundations.ConfigSpace

@[expose] public section

open MeasureTheory TopologicalSpace


namespace StatMech

namespace ConfigSpace

variable {E : Type*}


def eval (e : E) (ω : ConfigSpace E) : Bool := ω e

end ConfigSpace
end StatMech
