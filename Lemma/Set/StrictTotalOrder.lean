import Mathlib
import sympy.Basic
import sympy.atlas.Order.StrictTotalOrder
open MathlibExt.Order


/--
[StrictTotalOrder.ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/StrictTotalOrder.lean)
-/
@[path]
private lemma StrictTotalOrder_ext_eq
  {T T' : StrictTotalOrder α}
-- given
  (h : T.lt = T'.lt) :
-- imply
  T = T' := by
-- proof
  apply MathlibExt.Order.StrictTotalOrder.ext h


-- created on 2026-10-20
