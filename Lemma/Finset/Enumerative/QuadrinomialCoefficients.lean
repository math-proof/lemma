import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.QuadrinomialCoefficients
open scoped BigOperators
open MetaMathlibExt


/--
[quadrinomialCoeff_eq_zhangVSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QuadrinomialCoefficients.lean)
-/
@[path]
private lemma quadrinomialCoeff_eq_zhangVSum_eq
  {n : ℕ} :
-- imply
  quadrinomialCoeff n = zhangVSum n 1 1 0 0 0 := by
-- proof
  apply MetaMathlibExt.quadrinomialCoeff_eq_zhangVSum n


-- created on 2026-10-20
