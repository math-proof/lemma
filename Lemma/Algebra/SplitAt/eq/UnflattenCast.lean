import stdlib.List.Vector
import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
open Algebra


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (d : ℕ) :
-- imply
  have h : List.Vector α s.prod = List.Vector α ((s.take d).prod * (s.drop d).prod) := by rw [Prod.eq.MulProdTake__ProdDrop]
  v.splitAt d = (cast h v).unflatten := by
-- proof
  simp [List.Vector.splitAt]


-- created on 2025-07-12
