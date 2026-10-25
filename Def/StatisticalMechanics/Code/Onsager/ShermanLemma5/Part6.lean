/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part6


namespace StatMech.Onsager

open Matrix BigOperators


noncomputable def ons_m {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) : Fin n :=
  if h : (ons_mSet e rev v).Nonempty then (ons_mSet e rev v).max' h else 0


noncomputable def ons_surgery {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) : Fin n → E :=
  if (∃ i, v i = e) ∧ (∃ j, v j = rev e) then
    ons_revSeg rev (ons_l e rev v) (ons_m e rev v) v
  else v


end StatMech.Onsager
