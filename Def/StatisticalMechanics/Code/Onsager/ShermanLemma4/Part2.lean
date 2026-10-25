/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part2


namespace StatMech.Onsager

open Matrix BigOperators Finset

section Orbit

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]


noncomputable def ons_orbitCard (r : Fin n → E) : ℕ :=
  (Finset.univ.filter (fun v => ons_rep v = r)).card


end Orbit
end StatMech.Onsager
