import Lemma.List.AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop
open List


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (i : Fin (s.take d).prod)
  (j : Fin (s.drop d).prod) :
-- imply
  i * (s.drop d).prod + j < s.prod := by
-- proof
  apply AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop <;>
    simp


-- created on 2025-07-08
