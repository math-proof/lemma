import Lemma.Algebra.Gt_Sub_1.of.Ge
import Lemma.Algebra.Gt_Sub_1.of.Ge.Gt_0
import Lemma.Algebra.LengthTail.gt.Sub_1.of.GtLength.Gt_0
import Lemma.Algebra.Ge.of.Gt_Sub_1
import Lemma.Algebra.Sub.gt.Zero.is.Gt
open Algebra


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : i > 1)
  (h₁ : s.length ≥ i) :
-- imply
  s.tail.length ≥ i - 1 := by
-- proof
  apply Ge.of.Gt_Sub_1
  have h₁ := Gt_Sub_1.of.Ge.Gt_0 (show s.length > 0 by linarith) h₁
  apply LengthTail.gt.Sub_1.of.GtLength.Gt_0 _ h₁
  apply Sub.gt.Zero.of.Gt.nat h₀


-- created on 2025-05-05
-- updated on 2025-05-06
