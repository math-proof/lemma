import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.AbGeneralizedFibonacciSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[AbGeneralizedFibonacciSequence.ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AbGeneralizedFibonacciSequence.lean)
-/
@[path]
lemma AbGeneralizedFibonacciSequence.ext
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
-- updated on 2026-10-23
