import Mathlib
import sympy.Basic
import Instance.Combinatorics.Words.EquilibriousWord
open MetaMathlibExt


namespace MetaMathlibExt

/--
[isEquilibriousWord_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/EquilibriousWord.lean)
-/
@[path]
lemma isEquilibriousWord_reverse
  {u : List (Fin 2)} :
-- imply
  IsEquilibriousWord u.reverse ↔ IsEquilibriousWord u := by
-- proof
  unfold IsEquilibriousWord
  rw [List.count_reverse, List.count_reverse]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
