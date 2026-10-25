/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma5


namespace StatMech.Onsager

open Matrix BigOperators


noncomputable def ons_loopSetBoth {E} [Fintype E] [DecidableEq E] {n : ℕ}
    (a b : E) : Finset (Fin n → E) :=
  {v ∈ (Finset.univ : Finset (Fin n → E)) | (∃ i, v i = a) ∧ (∃ j, v j = b)}


end StatMech.Onsager
