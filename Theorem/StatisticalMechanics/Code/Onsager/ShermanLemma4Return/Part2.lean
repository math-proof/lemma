/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma4Return


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section FirstReturn

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]


theorem ons_firstReturn_root {e : E} {rev : E → E} {v : Fin n → E}
    (h : ons_isFirstReturn e rev v) : v 0 = e := h.1


theorem ons_firstReturn_unique {e : E} {rev : E → E} {v : Fin n → E}
    (h : ons_isFirstReturn e rev v) {k : Fin n} (hk : k ≠ 0) : v k ≠ e := h.2.1 k hk


theorem ons_firstReturn_avoids {e : E} {rev : E → E} {v : Fin n → E}
    (h : ons_isFirstReturn e rev v) (k : Fin n) : v k ≠ rev e := h.2.2 k


theorem ons_firstReturn_visits_once [DecidableEq (Fin n → E)] {e : E} {rev : E → E}
    {v : Fin n → E} (h : ons_isFirstReturn e rev v) :
    (Finset.univ.filter (fun k : Fin n => v k = e)) = {0} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hk
    by_contra hne
    exact ons_firstReturn_unique h hne hk
  · rintro rfl
    exact ons_firstReturn_root h


end FirstReturn
end StatMech.Onsager
