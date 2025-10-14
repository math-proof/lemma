import Lemma.List.EqRotateRotate.of.Le_Length
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_s : L = s.length)
  (h_i : i ≤ s.length) :
-- imply
  (s.rotate i).rotate (L - i) = s := by
-- proof
  rw [h_s]
  apply EqRotateRotate.of.Le_Length h_i


-- created on 2025-10-14
