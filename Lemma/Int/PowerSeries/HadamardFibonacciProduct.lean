import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PowerSeries.HadamardFibonacciProduct
open MetaMathlibExt


/--
[hadamard_fibonacci_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HadamardFibonacciProduct.lean)
-/
@[path]
private lemma hadamard_fibonacci_product_eq
  [CommRing R]
  {a b : R}
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  let f := by
-- proof
  apply MetaMathlibExt.hadamard_fibonacci_product R a b n hn


-- created on 2026-10-20
