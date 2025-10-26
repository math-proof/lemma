import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Nat.Mul
open Nat Rat


@[main, comm]
private lemma main
  [CommGroup α]
  {a b : α} :
-- imply
  a / b = b⁻¹ * a := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [Mul.comm]


-- created on 2024-11-29
