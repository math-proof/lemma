/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation.Part3
import Theorem.StatisticalMechanics.Code.Onsager.ShermanHlam
import Theorem.StatisticalMechanics.Code.Onsager.ShermanBucketCancellation


namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def rootedIndicator (Lambda : Matrix E E ℂ) (e r : E)
    (w : List E) : ℂ :=
  Set.indicator {w | ons_validRootedList e r w}
    (ons_rootedListTerm Lambda e) w

end StatMech.Onsager
