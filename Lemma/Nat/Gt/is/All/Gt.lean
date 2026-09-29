import Lemma.Tensor.All_Gt.is.Gt.Stack
import Lemma.Tensor.EqStack_Get
open Tensor


@[main]
private lemma main
  [Preorder α]
  {x y : Tensor α (n :: s)} :
-- imply
  x > y ↔ ∀ i : Fin n, x[i] > y[i] := by
-- proof
  constructor
  · intro h
    rw [← EqStack_Get x, ← EqStack_Get y] at h
    exact All_Gt.is.Gt.Stack.mpr h
  · intro h
    have := All_Gt.is.Gt.Stack.mp h
    rwa [EqStack_Get, EqStack_Get] at this


-- created on 2026-09-27
