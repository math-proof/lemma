import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Transcription.Comparator
open CPythonListsort


namespace CPythonListsort

/--
[iflt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Comparator.lean)
-/
@[path]
lemma iflt_eq
  {lt : BoolComparator α}
  {x y : α} :
-- imply
  iflt lt x y = lt x y :=
-- proof
  rfl

end CPythonListsort


-- created on 2026-10-23
