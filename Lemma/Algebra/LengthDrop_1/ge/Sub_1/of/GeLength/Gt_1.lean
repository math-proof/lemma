import Lemma.Algebra.Tail.eq.Drop_1
import Lemma.Algebra.LengthTail.ge.Sub_1.of.GeLength.Gt_0
open Algebra


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : i > 1)
  (h₁ : s.length ≥ i) :
-- imply
  (s.drop 1).length ≥ i - 1 := by
-- proof
  rw [Drop_1.eq.Tail]
  apply LengthTail.ge.Sub_1.of.GeLength.Gt_0 h₀ h₁


-- created on 2025-05-06
