import Lemma.List.EqRotateRotate.of.GeLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_s : L = s.length)
  (h_i : s.length ≥ i) :
-- imply
  (s.rotate i).rotate (L - i) = s := by
-- proof
  rw [h_s]
  apply EqRotateRotate.of.GeLength h_i


-- created on 2025-10-14
