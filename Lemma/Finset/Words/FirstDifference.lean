import Mathlib
import sympy.Basic
import Def.Combinatorics.Words.FirstDifference
open MetaMathlibExt


namespace MetaMathlibExt

/--
[length_firstDifferenceList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FirstDifference.lean)
-/
@[path]
lemma length_firstDifferenceList
  {w : List (ZMod 2)} :
-- imply
  (firstDifferenceList w).length = w.length - 1 := by
-- proof
  cases w <;> simp [firstDifferenceList]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
