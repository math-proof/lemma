/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part5


namespace CookLevin

open TuringMachine NPCompleteness

/-- `conjoinClauses cs` evaluates to true under `σ` iff every clause in `cs` does. -/
lemma conjoinClauses_eval : ∀ (cs : List BoolFormula) (_ : cs ≠ []) (σ : BoolAssignment),
    (conjoinClauses cs).eval σ = true ↔ ∀ c ∈ cs, c.eval σ = true
  | [c], _, σ => by simp [conjoinClauses]
  | c :: d :: ds, _, σ => by
    simp only [conjoinClauses, BoolFormula.eval, Bool.and_eq_true]
    rw [conjoinClauses_eval (d :: ds) (List.cons_ne_nil d ds) σ]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨hc, hrest⟩ x (rfl | hx)
      · exact hc
      · exact hrest x hx
    · intro h; exact ⟨h c (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

end CookLevin
