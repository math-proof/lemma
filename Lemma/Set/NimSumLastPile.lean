import Mathlib
import Initialize.Tactic.Attr.Basic
import Batteries.Data.Nat.Bitwise.Lemmas


namespace MetaMathlibExt

/--
[nim_sum_eq_zero_iff_last_eq_xor_fold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/NimSumLastPile.lean)
-/
@[path]
lemma nim_sum_eq_zero_iff_last_eq_xor_fold
  {preceding : List Nat}
  {last : Nat} :
-- imply
  List.foldl Nat.xor 0 (preceding ++ [last]) = 0 ↔ last = List.foldl Nat.xor 0 preceding := by
-- proof
  rw [List.foldl_concat, Nat.xor_eq]
  constructor
  · intro h
    have h2 : (List.foldl Nat.xor 0 preceding) ^^^ last
      = (List.foldl Nat.xor 0 preceding) ^^^ (List.foldl Nat.xor 0 preceding) := by
      rw [h, Nat.xor_self]
    exact Nat.xor_right_inj.mp h2
  · intro h
    rw [h, Nat.xor_self]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
