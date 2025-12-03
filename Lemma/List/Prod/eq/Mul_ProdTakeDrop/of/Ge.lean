import Lemma.List.Drop.eq.DropDrop__Sub.of.Ge
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  
  (h_d : i ≥ d) :
-- imply
  s.prod = (s.take (i - d)).prod * (((s.drop (i - d)).take (d + 1)).prod * (s.tail.drop i).prod) := by
-- proof
  simp
  rw [Drop.eq.DropDrop__Sub.of.Ge (show i + 1 ≥ i - d by omega)]
  rw [show i + 1 - (i - d) = d + 1 by omega]
  rw [MulProdS.eq.ProdAppend]
  simp


-- created on 2025-12-03
