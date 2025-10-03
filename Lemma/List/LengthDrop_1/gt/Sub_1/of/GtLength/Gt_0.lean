import Lemma.List.Tail.eq.Drop_1
import Lemma.List.LengthTail.gt.Sub_1.of.GtLength.Gt_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : i > 0)
  (h₁ : s.length > i) :
-- imply
  (s.drop 1).length > i - 1 := by
-- proof
  rw [Drop_1.eq.Tail]
  apply LengthTail.gt.Sub_1.of.GtLength.Gt_0 h₀ h₁


-- created on 2025-05-05
