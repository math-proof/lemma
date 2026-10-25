/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/StrictTotalOrder.lean -/

import Mathlib.Order.Defs.Unbundled
import Structure.Order.StrictTotalOrder
/-! # Strict total orders

Shared bundle for strict preferences, used by matching and social-choice developments.
-/


namespace MathlibExt.Order

/-- The relation of a `StrictTotalOrder` is a strict total order in Mathlib's unbundled sense, so
generic strict-order lemmas apply to `T.lt`. -/
instance StrictTotalOrder.isStrictTotalOrder {α : Type*} (T : StrictTotalOrder α) :
    IsStrictTotalOrder α T.lt where
  irrefl := T.irrefl
  trans _ _ _ := T.trans
  trichotomous := fun _ _ hab hba =>
    Classical.byContradiction fun h => (T.total h).elim hab hba

end MathlibExt.Order
