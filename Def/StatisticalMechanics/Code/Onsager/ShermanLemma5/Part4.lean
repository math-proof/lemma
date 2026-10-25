/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part4


namespace StatMech.Onsager

open Matrix BigOperators


noncomputable def ons_hitSet {E} [DecidableEq E] {n : ℕ} (e : E) (rev : E → E)
    (v : Fin n → E) : Finset (Fin n) :=
  {k | v k = e ∨ v k = rev e}

end StatMech.Onsager
