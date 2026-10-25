/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Finset.Card
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset
open Finset MulAction
open scoped Pointwise


namespace SpernerProperty

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

noncomputable def quotientPosetRank (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) :
    QuotientPoset n G → ℕ :=
  Quotient.lift (fun S : Finset (Fin n) => S.card)
    (fun _ _ h => card_eq_of_orbitRel h)

end SpernerProperty
