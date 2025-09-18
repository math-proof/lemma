import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
import Lemma.Algebra.Dvd_Mul
open Algebra


@[main]
private lemma main
-- given
  (s : List ℕ)
  (d : ℕ) :
-- imply
  (s.drop d).prod ∣ s.prod := by
-- proof
  rw [Prod.eq.MulProdTake__ProdDrop s d]
  apply Dvd_Mul


-- created on 2025-07-09
