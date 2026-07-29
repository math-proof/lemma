import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetMap.eq.MapGet
import sympy.matrices.expressions.special
open Tensor


@[main, comm]
private lemma main
  {f : α → β}
-- given
  (X : Fin n → Tensor α s) :
-- imply
  ([i < n] X i).map f = [i < n] ((X i).map f) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  rw [EqGetStack.fn.fin]
  erw [GetMap.eq.MapGet.fin (i := ⟨i, by grind⟩)]
  congr 1
  rw [EqGetStack.fn.fin]
  rfl


-- created on 2026-07-29
