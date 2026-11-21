import Theorem.List.EqCons_Tail.of.GtLength_0
import Theorem.List.ProdCons.eq.Mul_Prod
open List


/--
| attributes | lemma |
| :---: | :---: |
| path | List.Prod.eq.Mul_ProdTail.of.GtLength_0 |
| comm | List.Mul_ProdTail.eq.Prod.of.GtLength_0 |
-/
@[path, comm]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.prod = s[0] * s.tail.prod := by
-- proof
  conv_lhs => rw [Eq_Cons_Tail.of.GtLength_0 h]
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-06-09
-- updated on 2026-11-21
