import Lemma.Algebra.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
open Algebra


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_i : i < (s.take d).prod)
  (h_j : j < (s.drop d).prod) :
-- imply
  i * (s.drop d).prod + j < s.prod := by
-- proof
  have := AddMul.lt.Mul.of.Lt.Lt h_i h_j
  convert this
  apply Prod.eq.MulProdTake__ProdDrop


-- created on 2025-07-08
