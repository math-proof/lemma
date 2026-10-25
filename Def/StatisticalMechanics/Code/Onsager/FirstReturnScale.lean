/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FirstReturnScale.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation.Part3


namespace StatMech.Onsager

open Matrix BigOperators

def ons_scaleColumns {E : Type*} [DecidableEq E]
    (S : Finset E) (t : ℂ) (Lambda : Matrix E E ℂ) : Matrix E E ℂ :=
  fun i j => if j ∈ S then t * Lambda i j else Lambda i j

end StatMech.Onsager
