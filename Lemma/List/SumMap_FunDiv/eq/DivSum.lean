import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (x : List α)
  (a : α) :
-- imply
  (x.map (. / a)).sum = x.sum / a := by
-- proof
  induction x with
  | nil =>
    simp [Div.eq.Mul_Inv]
  | cons b xs ih =>
    simp [Div.eq.Mul_Inv] at ih ⊢
    rw [ih]
    apply AddMulS.eq.MulAdd


-- created on 2025-10-07
