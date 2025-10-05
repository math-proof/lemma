import Lemma.Algebra.LtAdd.of.Lt_Sub
open Algebra


@[main]
private lemma main
  {s : List α}
-- given
  (h : i < s.length - 1) :
-- imply
  have : i < s.tail.length := by simp_all
  s.tail[i] = s[i + 1] := by
-- proof
  induction s with
  | nil =>
    contradiction
  | cons =>
    simp_all


@[main]
private lemma fin
  {s : List α}
-- given
  (h : i < s.length - 1) :
-- imply
  have hi : i < s.tail.length := by simp_all
  s.tail.get ⟨i, hi⟩ = s.get ⟨i + 1, LtAdd.of.Lt_Sub.nat h⟩ := by
-- proof
  apply main h


-- created on 2025-10-05
