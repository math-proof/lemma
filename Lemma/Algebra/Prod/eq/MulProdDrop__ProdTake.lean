import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma main
  [CommMonoid α]
-- given
  (v : List α)
  (i : ℕ) :
-- imply
  v.prod = (v.drop i).prod * (v.take i).prod := by
-- proof
  
  rw [Prod.eq.MulProdTake__ProdDrop v i]
  apply Mul.comm


-- created on 2025-07-12
