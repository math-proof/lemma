/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.NumberTheoryI.code.FractionalIdeals.Part2
open nonZeroDivisors


section PrincipalFractionalIdealProps

variable (A : Type*) [CommRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

instance IdealGroup.commGroup : CommGroup (IdealGroup A K) := inferInstance

end PrincipalFractionalIdealProps
