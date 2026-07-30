import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Repeat.as.Resize.of.GtLength
open Bool Tensor


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  X.repeat d n = X.resize d (n * s[d]) := by
-- proof
  apply Eq.of.SEq
  simpa using Repeat.as.Resize.of.GtLength d.isLt X n


-- created on 2026-07-30
