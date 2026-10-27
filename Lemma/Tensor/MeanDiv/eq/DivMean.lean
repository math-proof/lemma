import Lemma.Tensor.SumDiv.eq.DivSum
import Lemma.Tensor.DivDiv
import Def.Data.Holor.Mean
open Tensor


@[path]
private lemma main
  [Semifield α]
-- given
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (X / n).mean = X.mean / n := by
-- proof
  simp [Tensor.mean]
  rw [SumDiv.eq.DivSum]
  repeat rw [Div.eq.Div_GetData_0]
  rw [DivDiv]


-- created on 2025-08-29
-- updated on 2026-10-26
