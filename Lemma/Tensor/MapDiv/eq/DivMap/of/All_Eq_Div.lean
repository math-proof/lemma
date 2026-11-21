import Instance.Data.Tensor.Defs.Part2
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.MapDiv.eq.DivMap.of.All_Eq_Div
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.MapDiv.eq.DivMap.of.All_Eq_Div |
| comm | Tensor.DivMap.eq.MapDiv.of.All_Eq_Div |
-/
@[path, comm]
private lemma main
  [Div α]
  [Div β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a / b) = f a / f b)
  (A : Tensor α s)
  (b : α) :
-- imply
  (A / b).map f = A.map f / f b := by
-- proof
  apply Eq.of.EqDataS
  simp [Tensor.map]
  apply MapDiv.eq.DivMap.of.All_Eq_Div hf


-- created on 2026-08-16
-- updated on 2026-11-20
