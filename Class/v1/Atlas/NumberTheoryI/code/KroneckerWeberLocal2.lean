/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part8
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GroupCounts


noncomputable section

namespace KroneckerWeberLocal2

class IsCyclicExtension (F : Type*) (E : Type*) [Field F] [Field E]
    [Algebra F E] : Prop where
  isGalois : IsGalois F E
  isCyclic : IsCyclic (E ≃ₐ[F] E)

end KroneckerWeberLocal2
end
