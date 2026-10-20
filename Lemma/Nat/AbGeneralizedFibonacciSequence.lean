import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.AbGeneralizedFibonacciSequence
open MetaMathlibExt


/--
[AbGeneralizedFibonacciSequence.ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AbGeneralizedFibonacciSequence.lean)
-/
@[path]
private lemma AbGeneralizedFibonacciSequence_ext_eq
  {x y : AbGeneralizedFibonacciSequence}
-- given
  (ha : x.a = y.a)
  (hb : x.b = y.b)
  (hF : x.F = y.F) :
-- imply
  x = y := by
-- proof
  apply MetaMathlibExt.AbGeneralizedFibonacciSequence.ext ha hb hF


-- created on 2026-10-20
