/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part5


namespace StatMech.Onsager

open Matrix BigOperators


noncomputable def ons_l {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) : Fin n :=
  if h : (ons_hitSet e rev v).Nonempty then (ons_hitSet e rev v).min' h else 0


noncomputable def ons_mSet {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) : Finset (Fin n) :=
  {j | v j = rev (v (ons_l e rev v))}

end StatMech.Onsager
