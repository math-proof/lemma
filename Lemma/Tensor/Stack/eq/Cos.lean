import sympy.tensor.functions
import Lemma.Tensor.Eq_Stack
import Lemma.Tensor.MapStack.eq.Stack_Map
open Tensor


@[main]
private lemma main
  [Cos α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  [i < n] X[i].cos = X.cos := by
-- proof
  conv_rhs => rw [Eq_Stack X]
  exact (MapStack.eq.Stack_Map (fun i : Fin n => X[i])).symm


-- created on 2023-06-08
-- updated on 2026-08-23
