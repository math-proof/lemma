import Lemma.Tensor.All_Ge.is.Ge.Stack
import Lemma.Tensor.EqStack_Get
open Tensor


@[path]
private lemma main
  [LE α]
  {x y : Tensor α (n :: s)} :
-- imply
  x ≥ y ↔ ∀ i : Fin n, x[i] ≥ y[i] := by
-- proof
  constructor
  ·
    intro h
    rw [← EqStack_Get x, ← EqStack_Get y] at h
    exact All_Ge.is.Ge.Stack.mpr h
  ·
    intro h
    have := All_Ge.is.Ge.Stack.mp h
    rwa [EqStack_Get, EqStack_Get] at this


-- created on 2022-03-31
