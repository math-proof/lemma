import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MedianGenocchiNumber
open scoped BigOperators
open MetaMathlibExt


/--
[medianGenocchiOdd_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianGenocchiNumber.lean)
-/
@[path]
private lemma medianGenocchiOdd_zero_eq
  :
-- imply
  medianGenocchiOdd 0 = 1 := by
-- proof
  apply MetaMathlibExt.medianGenocchiOdd_zero

/--
[medianGenocchiOdd_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianGenocchiNumber.lean)
-/
@[path]
private lemma medianGenocchiOdd_one_eq
  :
-- imply
  medianGenocchiOdd 1 = -1 := by
-- proof
  apply MetaMathlibExt.medianGenocchiOdd_one


-- created on 2026-10-20
