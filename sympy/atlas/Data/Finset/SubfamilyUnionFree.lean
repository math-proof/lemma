/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Finset/SubfamilyUnionFree.lean -/

/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Union-free families of finite sets

A family of finite sets is union-free over its subfamilies when no member
is the union of other members of the family.
-/

namespace Finset

/-- A family `F` is union-free over a subfamily: no member is the union of
other members. -/
def SubfamilyUnionFree {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ T ⊆ F.erase A, T.Nonempty → T.sup id ≠ A

end Finset
