import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length
import sympy.tensor.stack
open Tensor Bool


@[main]
private lemma main
-- given
  (h : s.length > d)
  (f : Fin n → Tensor α s)
  (i : Fin s[d]) :
-- imply
  ([k < n] f k).select ⟨d + 1, by simpa⟩ i = [k < n] (f k).select ⟨d, h⟩ i := by
-- proof
  apply Eq.of.All_EqGetS
  intro k
  rw [EqGetStack.fn]
  apply Eq.of.SEq
  have := GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length (i := i) (j := k) (d := d) (by grind) (by simp) (by simp) ([k < n] f k)
  apply this.trans
  rw [EqGetStack.fn.fin]
  rfl


-- created on 2025-11-11
