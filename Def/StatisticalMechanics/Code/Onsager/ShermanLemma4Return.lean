module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
public import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3
public import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4Return


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section FirstReturn

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]


def ons_isFirstReturn (e : E) (rev : E → E) (v : Fin n → E) : Prop :=
  v 0 = e ∧ (∀ k : Fin n, k ≠ 0 → v k ≠ e) ∧ (∀ k : Fin n, v k ≠ rev e)


end FirstReturn
end StatMech.Onsager
