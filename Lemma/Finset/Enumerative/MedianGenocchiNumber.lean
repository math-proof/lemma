import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MedianGenocchiNumber
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[medianGenocchiOdd_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianGenocchiNumber.lean)
-/
@[path]
lemma medianGenocchiOdd_zero
  :
-- imply
  medianGenocchiOdd 0 = 1 := by
-- proof
  simp [medianGenocchiOdd]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[medianGenocchiOdd_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianGenocchiNumber.lean)
-/
@[path]
lemma medianGenocchiOdd_one
  :
-- imply
  medianGenocchiOdd 1 = -1 := by
-- proof
  have h : genocchiNumberViaBernoulli 2 = -1 := by
    rw [genocchiNumberViaBernoulli, bernoulli_two]
    norm_num
  simp [medianGenocchiOdd, h]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
