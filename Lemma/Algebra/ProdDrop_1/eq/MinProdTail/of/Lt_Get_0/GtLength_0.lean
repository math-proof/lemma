import Lemma.Algebra.EqMin.of.Le
import Lemma.Algebra.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Algebra.Le_SubMulS.of.Lt
open Algebra


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0]) :
-- imply
  (s.drop 1).prod = s.tail.prod ⊓ (s.prod - i * s.tail.prod) := by
-- proof
  rw [EqMin.of.Le]
  ·
    simp
  ·
    rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h_s]
    apply Le_SubMulS.of.Lt h_i


-- created on 2025-07-11
