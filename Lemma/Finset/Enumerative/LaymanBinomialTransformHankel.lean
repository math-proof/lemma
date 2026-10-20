import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.LaymanBinomialTransformHankel
open MetaMathlibExt


/--
[layman_binomial_transform_hankel_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean)
-/
@[path]
private lemma layman_binomial_transform_hankel_invariant_eq
  {a : ℕ → ℤ} :
-- imply
  hankelTransform (binomialTransform a) = hankelTransform a := by
-- proof
  apply MetaMathlibExt.layman_binomial_transform_hankel_invariant a


-- created on 2026-10-20
