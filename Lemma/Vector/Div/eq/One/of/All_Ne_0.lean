import Instance.Data.Vector.Basic.Arithmetic
import Lemma.Vector.Eq.is.All_EqGetS
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.Div.eq.One.of.All_Ne_0 |
| fin 1 | Vector.Div.eq.One.of.All_Ne_0.fin |
-/
@[path, fin 1]
private lemma main
  [GroupWithZero α]
  {x : List.Vector α n}
-- given
  (h : ∀ i : Fin n, x[i] ≠ 0) :
-- imply
  x / x = 1 := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGet1_1]
  rw [GetDiv.eq.DivGetS]
  apply div_self (h i)


-- created on 2025-11-28
-- updated on 2026-11-20
