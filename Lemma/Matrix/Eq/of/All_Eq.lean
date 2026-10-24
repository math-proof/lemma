import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.DiscreteSpectrum
open scoped BigOperators


/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private lemma ext_eq
-- given
  {S T : NonnegativeDiscreteSpectrum}
  (h : ∀ j, S j = T j) :
-- imply
  S = T := by
-- proof
  apply NonnegativeDiscreteSpectrum.ext h

-- created on 2026-10-10
-- updated on 2026-10-23
