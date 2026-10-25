/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma4


namespace StatMech.Onsager

open Matrix BigOperators Finset

section Orbit

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]


theorem ons_rep_rel (v : Fin n → E) :
    (ons_orbitSetoid E n).r (ons_rep v) v :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (ons_orbitSetoid E n) v))


end Orbit
end StatMech.Onsager
