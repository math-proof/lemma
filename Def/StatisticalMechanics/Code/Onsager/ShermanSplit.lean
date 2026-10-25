/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section EdgeWeight

variable {E : Type*}


noncomputable def ons_edgeWeight (Λ : Matrix E E ℂ) : List E → ℂ
  | [] => 1
  | [_] => 1
  | a :: b :: t => Λ a b * ons_edgeWeight Λ (b :: t)

end EdgeWeight
end StatMech.Onsager
