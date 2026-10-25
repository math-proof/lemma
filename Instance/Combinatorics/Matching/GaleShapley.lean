/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Abbrev.Combinatorics.Matching.GaleShapley
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

namespace StrictTotalOrder

/-- Compatibility instance for the former `GaleShapley` order instance.

For new code, use `MathlibExt.Order.StrictTotalOrder.isStrictTotalOrder` directly. -/
instance isStrictTotalOrder {α : Type*} (T : StrictTotalOrder α) :
    IsStrictTotalOrder α T.lt :=
  MathlibExt.Order.StrictTotalOrder.isStrictTotalOrder T

end StrictTotalOrder
end MathlibExt.Combinatorics.Matching.GaleShapley
