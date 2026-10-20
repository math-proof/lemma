import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.NimSumLastPile
open MetaMathlibExt


/--
[nim_sum_eq_zero_iff_last_eq_xor_fold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/NimSumLastPile.lean)
-/
@[path]
private lemma nim_sum_eq_zero_iff_last_eq_xor_fold_eq
  {preceding : List Nat}
  {last : Nat} :
-- imply
  List.foldl Nat.xor 0 (preceding ++ [last]) = 0 ↔ last = List.foldl Nat.xor 0 preceding := by
-- proof
  apply MetaMathlibExt.nim_sum_eq_zero_iff_last_eq_xor_fold preceding last


-- created on 2026-10-20
