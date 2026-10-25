/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Every positive root $\alpha \in \Phi^+$ has unit length for the Coxeter form: $B(\alpha,\alpha) = 1$.
This follows from the fact that simple roots have unit length and the form is $W$-invariant. -/
theorem standardΦpos_form_eq_one (M : CoxeterMatrix B)
    (α : B → ℝ) (hα : α ∈ standardΦpos M) :
    CoxeterGroup.bilinForm M α α = 1 := by
  obtain ⟨⟨ws, s₀, hα_eq⟩, _⟩ := hα
  rw [hα_eq, sigmaWord_eq_wordSigma_reverse, CoxeterGroup.wordSigma_preserves_form,
      CoxeterGroup.bilinForm_e_e, CoxeterGroup.formVal_diag]

end TitsCone
