import Lemma.Tensor.All_Lt.is.Lt.Stack
import Lemma.Tensor.EqStack_Get
open Tensor


@[path]
private lemma main
  [Preorder α]
  {x y : Tensor α (n :: s)} :
-- imply
  x < y ↔ ∀ i : Fin n, x[i] < y[i] := by
-- proof
  constructor
  · intro h
    rw [← EqStack_Get x, ← EqStack_Get y] at h
    exact All_Lt.is.Lt.Stack.mpr h
  · intro h
    have := All_Lt.is.Lt.Stack.mp h
    rwa [EqStack_Get, EqStack_Get] at this


-- created on 2022-03-31
