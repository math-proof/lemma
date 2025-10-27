import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.DropAppend.eq.AppendDropS
open List


@[main]
private lemma main
-- given
  (h : i ≥ a.length)
  (b : List α) :
-- imply
  (a ++ b).drop i = b.drop (i - a.length) := by
-- proof
  rw [DropAppend.eq.AppendDropS]
  rw [Drop.eq.Nil.of.Ge_Length h]
  simp


-- created on 2025-10-03
