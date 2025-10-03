import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.MulMul
import Lemma.Algebra.ProdAppend.eq.MulProdS
import Lemma.List.EqAppendTake__Drop
import Lemma.Algebra.Mul
open Algebra List


@[main]
private lemma main
  [CommMonoid α]
-- given
  (s : List α)
  (n : α)
  (d : ℕ):
-- imply
  (s.take d).prod * (n * (s.drop d).prod) = n * s.prod := by
-- proof
  rw [Mul_Mul.eq.MulMul]
  rw [MulMul.comm]
  rw [MulProdS.eq.ProdAppend]
  rw [EqAppendTake__Drop]
  rw [Mul.comm]


-- created on 2025-07-17
