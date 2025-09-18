import stdlib.List
import Lemma.Basic


@[main]
private lemma main
-- given
  (a b : List α)
  (n : ℕ) :
-- imply
  (a ++ b).slice a.length n = b.take (n - a.length) := by
-- proof
  unfold List.slice List.array_slice
  aesop


-- created on 2025-05-18
