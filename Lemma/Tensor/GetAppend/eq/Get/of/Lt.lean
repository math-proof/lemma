import Lemma.Tensor.GetAppend.eq.Get
open Tensor


@[main]
private lemma main
-- given
  (h : i < n)
  (a : Tensor α (n :: s))
  (b : Tensor α (m :: s)) :
-- imply
  have : i < n + m := by linarith
  (a ++ b)[i] = a[i] := by
-- proof
  let i : Fin n := ⟨i, h⟩
  have := GetAppend.eq.Get a b i
  simp_all
  assumption


-- created on 2025-06-01
-- updated on 2025-06-26
