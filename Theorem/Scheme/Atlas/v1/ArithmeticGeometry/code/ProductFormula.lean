module

public import Mathlib

public section


namespace NumberField

/--
[product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductFormula.lean)
-/
public theorem product_formula
  [Field K]
  [NumberField K]
  {x : K}
-- given
  (hx : x ≠ 0) :
-- imply
  (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 :=
-- proof
  prod_abs_eq_one hx

end NumberField


-- created on 2026-10-23
