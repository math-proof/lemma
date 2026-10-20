import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Words.EquilibriousWord
open MetaMathlibExt


/--
[isEquilibriousWord_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/EquilibriousWord.lean)
-/
@[path]
private lemma isEquilibriousWord_reverse_eq
  {u : List (Fin 2)} :
-- imply
  IsEquilibriousWord u.reverse ↔ IsEquilibriousWord u := by
-- proof
  apply MetaMathlibExt.isEquilibriousWord_reverse


-- created on 2026-10-20
