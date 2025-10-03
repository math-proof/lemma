import Lemma.List.Take.eq.Cons_TakeTail.of.GtLength_0.Gt_0
import Lemma.Algebra.ProdCons.eq.Mul_Prod
open Algebra List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : d > 0)
  (h_s : s.length > 0) :
-- imply
  s[0] ∣ (s.take d).prod := by
-- proof
  rw [Take.eq.Cons_TakeTail.of.GtLength_0.Gt_0 (by assumption) (by assumption)]
  rw [ProdCons.eq.Mul_Prod]
  simp


-- created on 2025-07-06
