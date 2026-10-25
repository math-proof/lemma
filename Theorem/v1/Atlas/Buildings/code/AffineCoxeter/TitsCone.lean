/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Mathlib.Data.Fintype.BigOperators
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- $\overline{C} \subseteq \mathcal U$: the closed fundamental chamber is in the Tits cone
(realized as the orbit of $\overline{C}$ under the empty word). -/
theorem titsFundamentalClosure_subset_titsCone (M : CoxeterMatrix B) :
    titsFundamentalClosure M ⊆ titsConeSet M := by
  intro x hx
  simp only [titsConeSet, Set.mem_setOf_eq, titsFundamentalClosure, Set.mem_setOf_eq] at *
  exact ⟨x, hx, [], rfl⟩

/-- The dual action is an involution: $\sigma^*_s \circ \sigma^*_s = \mathrm{id}$. -/
theorem dualSigma_involutive (M : CoxeterMatrix B) (s : B) (x : B → ℝ) :
    dualSigma M s (dualSigma M s x) = x := by
  ext t
  simp only [dualSigma, formVal_diag]
  ring

end TitsCone
