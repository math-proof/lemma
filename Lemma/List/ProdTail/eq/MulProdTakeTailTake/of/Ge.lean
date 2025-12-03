import Lemma.List.DropTail.eq.Drop
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.Prod.eq.Mul_ProdTakeDrop.of.Ge
import Lemma.List.TailTake.eq.TakeTail
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.Nat.SubAddS.eq.Sub
open List Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  
  (h_d : i ≥ d) :
-- imply
  s.tail.prod = (((s.take (i + 1 + 1)).tail.take (i - d)).prod * (((s.take (i + 1 + 1)).drop (i + 1 - d)).prod * (s.drop (i + 1 + 1)).prod)) := by
-- proof
  rw [TailTake.eq.TakeTail]
  rw [TakeTake.eq.Take.of.Gt (by omega)]
  rw [DropTake.eq.TakeDrop]
  rw [show i + 1 - d = i - d + 1 by omega]
  repeat rw [Drop.eq.DropTail]
  rw [SubAddS.eq.Sub]
  rw [show i + 1 - (i - d) = d + 1 by omega]
  rw [Prod.eq.Mul_ProdTakeDrop.of.Ge h_d]


-- created on 2025-12-03
