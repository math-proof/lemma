/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneCoherence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Def.v1.Atlas.TensorCategories.code.MacLaneCoherence
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


namespace EGNO.MacLaneCoherence

section Theorem_1_9_1

/-- Theorem 1.9.1 (MacLane's Coherence Theorem): Any two morphisms built by composing
associativity and unit isomorphisms (and their inverses, possibly tensored with identities)
between the same source and target in a monoidal category are equal. -/
theorem Theorem_1_9_1 {C : Type*} {D : Type*} [Category D] [MonoidalCategory D]
    (f : C → D) {P₁ P₂ : FreeMonoidalCategory C} (g₁ g₂ : P₁ ⟶ P₂) :
    (FreeMonoidalCategory.project f).map g₁ = (FreeMonoidalCategory.project f).map g₂ := by
  congr 1
  exact Subsingleton.elim g₁ g₂

end Theorem_1_9_1
end EGNO.MacLaneCoherence
