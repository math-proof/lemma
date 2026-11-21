import Lemma.Rat.Div.eq.Mul_Inv
import Theorem.Nat.MulAdd.eq.AddMulS
open Nat Rat


/--
| attributes | lemma |
| :---: | :---: |
| path | Rat.DivAdd.eq.AddDivS |
| comm | Rat.AddDivS.eq.DivAdd |
-/
@[path, comm]
private lemma main
  [DivInvMonoid α]
  [Add α]
  [RightDistribClass α]
-- given
  (x y a : α) :
-- imply
  (x + y) / a = x / a + y / a := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [MulAdd.eq.AddMulS]


-- created on 2024-07-01
-- updated on 2026-11-21
