import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.WordFactorComplexity
open MetaMathlibExt


/--
[wordFactorComplexity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/WordFactorComplexity.lean)
-/
@[path]
private lemma wordFactorComplexity_zero_eq
  [Finite A]
  {w : ℕ → A} :
-- imply
  wordFactorComplexity w 0 = 1 := by
-- proof
  apply MetaMathlibExt.wordFactorComplexity_zero w


-- created on 2026-10-20
