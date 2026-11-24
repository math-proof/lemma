module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.CPythonListsort.Code.Transcription.Comparator

public section

open CPythonListsort


namespace CPythonListsort

/--
[iflt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Comparator.lean)
-/
@[path]
public lemma iflt_eq
  {lt : BoolComparator α}
  {x y : α} :
-- imply
  iflt lt x y = lt x y :=
-- proof
  rfl

end CPythonListsort


-- created on 2026-10-23
