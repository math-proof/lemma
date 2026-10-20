import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Words.FirstDifference
open MetaMathlibExt


/--
[length_firstDifferenceList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FirstDifference.lean)
-/
@[path]
private lemma length_firstDifferenceList_eq
  {w : List (ZMod 2)} :
-- imply
  (firstDifferenceList w).length = w.length - 1 := by
-- proof
  apply MetaMathlibExt.length_firstDifferenceList w


-- created on 2026-10-20
