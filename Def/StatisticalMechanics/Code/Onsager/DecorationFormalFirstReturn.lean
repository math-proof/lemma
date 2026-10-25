/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3


namespace StatMech.Onsager

open BigOperators Finset

section GenericReroot

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {n : ℕ} [NeZero n]

noncomputable def ons_invariantRerootTerm
    (weight : (Fin n → E) → ℂ) (e r : E) (loop : Fin n → E) : ℂ :=
  if (∀ j, loop j ≠ r) ∧ loop 0 = e then
    weight loop / (ons_visitCount e loop : ℂ)
  else 0

noncomputable def ons_invariantMarkedTerm
    (weight : (Fin n → E) → ℂ) (e r : E)
    (k : Fin n) (loop : Fin n → E) : ℂ :=
  if (∀ j, loop j ≠ r) ∧ loop k = e then
    weight loop / (ons_visitCount e loop : ℂ)
  else 0

end GenericReroot
end StatMech.Onsager
