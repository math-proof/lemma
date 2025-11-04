import Lemma.List.Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0
import Lemma.List.ProdCons.eq.Mul_Prod
open List


@[main]
private lemma main
  [Monoid M]
  {s : List M}
-- given
  (h_s : s.length > 0)
  (h : d > 0) :
-- imply
  s[0] ∣ (s.take d).prod := by
-- proof
  rw [Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0 (by assumption) (by assumption)]
  rw [ProdCons.eq.Mul_Prod]
  simp


-- created on 2025-07-06
