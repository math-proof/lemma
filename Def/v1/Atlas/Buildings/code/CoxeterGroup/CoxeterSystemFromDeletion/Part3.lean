/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion.Part3
open Function Set


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- The deletion condition for a family of generators $\mathtt{gen} : B \to W$:
whenever a word $\omega$ in $B$ can be shortened (its $\mathtt{gen}$-product
equals that of a strictly shorter word), there exist two indices $i < j$ in
$\omega$ whose deletion preserves the product. -/
def SatisfiesDeletionConditionGen (gen : B → W) : Prop :=
  ∀ (word : List B),
    (∃ (shorter : List B), shorter.length < word.length ∧
      (shorter.map gen).prod = (word.map gen).prod) →
    ∃ (i j : ℕ), i < j ∧ j < word.length ∧
      (((word.eraseIdx j).eraseIdx i).map gen).prod = (word.map gen).prod

end CoxeterSystemFromDeletion
