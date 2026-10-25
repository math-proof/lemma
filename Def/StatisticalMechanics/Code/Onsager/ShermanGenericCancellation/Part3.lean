/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanGenericCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanListSeries.Part2
import Theorem.StatisticalMechanics.Code.Onsager.ShermanReroot.Part4
import Theorem.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation.Part2


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def ons_rootedListTerm (Lambda : Matrix E E ℂ) (e : E)
    (w : List E) : ℂ :=
  ons_edgeWeight Lambda w / ((ons_firstReturnFactors e w).length : ℂ)

end StatMech.Onsager
