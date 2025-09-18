import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.NegMul.eq.MulNeg
import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main, comm]
private lemma nat
  (x a b : ℕ) :
-- imply
  (a - b) * x = a * x - b * x :=
-- proof
  Nat.sub_mul a b x


@[main, comm]
private lemma main
  [Ring α]
  (x a b : α) :
-- imply
  (a - b) * x = a * x - b * x := by
-- proof
  rw [Sub.eq.Add_Neg (a := a)]
  rw [← AddMulS.eq.MulAdd]
  rw [Sub.eq.Add_Neg]
  rw [NegMul.eq.MulNeg]


-- created on 2024-11-26
-- updated on 2025-03-31
