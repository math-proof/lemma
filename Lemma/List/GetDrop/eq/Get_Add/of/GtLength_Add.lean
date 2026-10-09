import Lemma.Nat.Lt_Sub.of.LtAdd
open Nat


@[path, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + j) :
-- imply
  have : j < (s.drop i).length := by simp_all [Lt_Sub.of.LtAdd.left]
  (s.drop i)[j] = s[i + j] := by
-- proof
  simp_all


-- created on 2025-06-07
-- updated on 2025-06-28
