import Lemma.Nat.LtAdd.of.Lt_Sub
open Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : i < s.length - 1) :
-- imply
  s.tail[i]'(by simpa) = s[i + 1] := by
-- proof
  grind


@[main]
private lemma fin
  {s : List α}
-- given
  (h : i < s.length - 1) :
-- imply
  s.tail.get ⟨i, by simpa⟩ = s.get ⟨i + 1, LtAdd.of.Lt_Sub h⟩ := by
-- proof
  apply main h


-- created on 2025-10-05
