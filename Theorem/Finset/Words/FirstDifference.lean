module

public import Mathlib
public import Def.Combinatorics.Words.FirstDifference

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[length_firstDifferenceList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FirstDifference.lean)
-/
public theorem length_firstDifferenceList
  {w : List (ZMod 2)} :
-- imply
  (firstDifferenceList w).length = w.length - 1 := by
-- proof
  cases w <;> simp [firstDifferenceList]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
