import Lemma.Rat.EqMulDiv.of.Ne_0
import Theorem.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.Eq.is.All_EqGetS
import Theorem.Vector.GetMul.eq.MulGetS
open Vector Rat


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.EqMulDiv.of.All_Ne_0 |
| fin 1 | Vector.EqMulDiv.of.All_Ne_0.fin |
-/
@[path, fin 1]
private lemma main
  [GroupWithZero α]
  {b : List.Vector α n}
-- given
  (h : ∀ i : Fin n, b[i] ≠ 0)
  (a : List.Vector α n) :
-- imply
  a / b * b = a := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [GetMul.eq.MulGetS]
  rw [GetDiv.eq.DivGetS]
  rw [EqMulDiv.of.Ne_0 (h i)]


-- created on 2025-12-30
-- updated on 2026-11-20
