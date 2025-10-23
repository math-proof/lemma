import Lemma.Nat.Lt_Sub.of.LtAdd
open Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > n + j) :
-- imply
  have : j < (s.drop n).length := by simp_all [Lt_Sub.of.LtAdd.left]
  (s.drop n)[j] = s[n + j] := by
-- proof
  simp_all


-- created on 2025-06-07
-- updated on 2025-06-28
