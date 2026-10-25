import Mathlib
import sympy.Basic
import Instance.Order.StrictTotalOrder
open MathlibExt.Order


namespace MathlibExt.Order

/--
[StrictTotalOrder.ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/StrictTotalOrder.lean)
-/
@[path]
lemma StrictTotalOrder.ext
  {T T' : StrictTotalOrder α}
-- given
  (h : T.lt = T'.lt) :
-- imply
  T = T' := by
-- proof
  cases T
  cases T'
  cases h
  rfl

end MathlibExt.Order


-- created on 2026-10-20
-- updated on 2026-10-23
