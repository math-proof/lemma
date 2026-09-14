import torch.stack
import Lemma.List.EqCons_Tail.of.NeLength_0
open List Tensor

/--
[masked_fill](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.masked_fill.html)
-/
def Tensor.masked_fill [Zero α] (X : Tensor α s) (d : ℤ) (cmp : ℤ → ℤ → Bool) : Tensor α s :=
  if h_s : s.length > 2 then
    cast
      (by
        rw [HeadD.eq.Get_0.of.NeLength_0 (by linarith)]
        rw [EqCons_Tail.of.NeLength_0 (by linarith)]
      )
      (Tensor.OfVector (X.toVector.map (·.masked_fill d cmp)))
  else if h_s : s.length < 2 then
    X
  else
    have h_s : s.length = 2 := by grind
    match h : s with
    | [m, n] =>
      [i < m] [j < n] (if cmp (j - i) d then 0 else (X.get ⟨i, by grind⟩).get ⟨j, by grind⟩)
