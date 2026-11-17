module

public import Mathlib
public import Structure.NumberTheory.AbGeneralizedFibonacciSequence

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[AbGeneralizedFibonacciSequence.ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AbGeneralizedFibonacciSequence.lean)
-/
public theorem AbGeneralizedFibonacciSequence.ext
  {x y : AbGeneralizedFibonacciSequence}
-- given
  (ha : x.a = y.a)
  (hb : x.b = y.b)
  (hF : x.F = y.F) :
-- imply
  x = y := by
-- proof
  cases x
  cases y
  cases ha
  cases hb
  cases hF
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
