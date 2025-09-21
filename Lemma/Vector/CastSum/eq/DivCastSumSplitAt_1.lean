import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Add α] [Zero α] [Div α]
  {s : List ℕ}
-- given
  (x : List.Vector α s.prod)
  (n : α) :
-- imply
  have h : List.Vector α (s.drop 1).prod = List.Vector α (s.eraseIdx 0).prod := by
    simp
  cast h ((x / n).splitAt 1).sum = cast h (x.splitAt 1).sum / n := by
-- proof
  unfold List.Vector.splitAt
  simp
  sorry


-- created on 2025-09-21
