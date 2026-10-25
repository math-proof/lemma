/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.Grade
import Mathlib.Order.Antichain
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty
open Finset


namespace SpernerProperty

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

abbrev BooleanPoset (n : ℕ) : Type := Finset (Fin n)

end SpernerProperty
