import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.List.Tail.eq.Drop_1
import Lemma.Nat.Add
open List Nat


@[main]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (d : ℕ) :
-- imply
  s.tail.prod = (s.tail.take d).prod * (s.drop (d + 1)).prod := by
-- proof
  rw [Tail.eq.Drop_1]
  rw [Add.comm]
  apply ProdDrop.eq.MulProdS


-- created on 2025-11-02
