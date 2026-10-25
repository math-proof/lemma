/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ShermanSplit


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section EdgeWeight

variable {E : Type*}


variable (Λ : Matrix E E ℂ)


@[simp] theorem ons_edgeWeight_nil : ons_edgeWeight Λ ([] : List E) = 1 := rfl


@[simp] theorem ons_edgeWeight_singleton (a : E) : ons_edgeWeight Λ [a] = 1 := rfl


theorem ons_edgeWeight_cons_cons (a b : E) (t : List E) :
    ons_edgeWeight Λ (a :: b :: t) = Λ a b * ons_edgeWeight Λ (b :: t) := rfl


theorem ons_edgeWeight_append_cons (u : List E) (b : E) (v : List E) :
    ons_edgeWeight Λ (u ++ b :: v)
      = ons_edgeWeight Λ (u ++ [b]) * ons_edgeWeight Λ (b :: v) := by
  induction u with
  | nil => simp
  | cons a u' ih =>
    cases u' with
    | nil =>
        show ons_edgeWeight Λ (a :: b :: v)
              = ons_edgeWeight Λ [a, b] * ons_edgeWeight Λ (b :: v)
        rw [ons_edgeWeight_cons_cons, ons_edgeWeight_cons_cons, ons_edgeWeight_singleton]
        ring
    | cons c u'' =>
        show ons_edgeWeight Λ (a :: c :: (u'' ++ b :: v))
              = ons_edgeWeight Λ (a :: c :: (u'' ++ [b])) * ons_edgeWeight Λ (b :: v)
        rw [ons_edgeWeight_cons_cons, ons_edgeWeight_cons_cons]
        rw [show ons_edgeWeight Λ (c :: (u'' ++ b :: v))
              = ons_edgeWeight Λ (c :: (u'' ++ [b])) * ons_edgeWeight Λ (b :: v) from ih]
        ring

end EdgeWeight
end StatMech.Onsager
