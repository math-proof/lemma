import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.SquareFreeWord
open MetaMathlibExt


/--
[IsSquareFreeWord.of_isInfix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/SquareFreeWord.lean)
-/
@[path]
private lemma IsSquareFreeWord_of_isInfix_eq
  {u v : List α}
-- given
  (hv : IsSquareFreeWord v)
  (huv : u.IsInfix v) :
-- imply
  IsSquareFreeWord u := by
-- proof
  apply MetaMathlibExt.IsSquareFreeWord.of_isInfix hv huv

/--
[isSquareFreeWord_iff_inits_tails](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/SquareFreeWord.lean)
-/
@[path]
private lemma isSquareFreeWord_iff_inits_tails_eq
  {w : List α} :
-- imply
  IsSquareFreeWord w ↔
    ∀ s ∈ w.tails.flatMap List.inits, ∀ x ∈ s.inits, x ≠ [] → s ≠ x ++ x := by
-- proof
  apply MetaMathlibExt.isSquareFreeWord_iff_inits_tails


-- created on 2026-10-20
