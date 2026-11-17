/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Grade
public import Mathlib.Order.Antichain
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty
@[expose] public section

open Finset


namespace SpernerProperty

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

abbrev BooleanPoset (n : ℕ) : Type := Finset (Fin n)

end SpernerProperty
