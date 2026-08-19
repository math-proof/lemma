import Lemma.Tensor.MapStack.eq.Stack_Map
import Lemma.Tensor.Stack.eq.AppendStackS
open Tensor


@[main]
private lemma main
  {n : ℕ}
  {f : α → β}
-- given
  (X : ℕ → Tensor α s) :
-- imply
  ([i < n + j] X i).map f = [i < n] ((X i).map f) ++ [i < j] ((X (n + i)).map f) := by
-- proof
  rw [MapStack.eq.Stack_Map]
  rw [Stack.eq.AppendStackS (fun i => (X i).map f)]


-- created on 2026-08-19
