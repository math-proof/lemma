import Lemma.Nat.Lt_Sub.of.LtAdd
open Nat


@[main]
private lemma main
  {i : ℕ}
  {s : List α}
-- given
  (h : i + 1 < s.length) :
-- imply
  i < s.tail.length := by
-- proof
  simp
  apply Lt_Sub.of.LtAdd h


-- created on 2025-06-24
