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
@[expose] public section

open Finset MulAction
open scoped Pointwise


namespace SpernerProperty

abbrev QuotientPoset (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) : Type :=
  orbitRel.Quotient G (Finset (Fin n))

end SpernerProperty
