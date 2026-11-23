/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Finset.Card
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset

@[expose] public section

open Finset MulAction
open scoped Pointwise


namespace SpernerProperty

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

noncomputable def quotientPosetRank (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) :
    QuotientPoset n G → ℕ :=
  Quotient.lift (fun S : Finset (Fin n) => S.card)
    (fun _ _ h => card_eq_of_orbitRel h)

end SpernerProperty
