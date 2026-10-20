import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MedianGenocchiDivisibility
open scoped BigOperators
open MetaMathlibExt


/--
[medianGenocchiOdd_divisibility](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianGenocchiDivisibility.lean)
-/
@[path]
private lemma medianGenocchiOdd_divisibility_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ∃ z : ℤ, medianGenocchiOdd (n + 1) = (2 : ℚ) ^ n * z ∧
    Int.ModEq 6 z (if Odd n then 1 else 4) := by
-- proof
  apply MetaMathlibExt.medianGenocchiOdd_divisibility n hn


-- created on 2026-10-20
