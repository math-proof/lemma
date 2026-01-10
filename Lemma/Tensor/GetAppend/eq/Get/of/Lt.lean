import Lemma.Tensor.GetAppend.eq.Get
open Tensor


@[main, fin]
private lemma main
-- given
  (h : i < n)
  (A : Tensor α (n :: s))
  (B : Tensor α (m :: s)) :
-- imply
  have : i < n + m := by linarith
  (A ++ B)[i] = A[i] := by
-- proof
  let i : Fin n := ⟨i, h⟩
  have := GetAppend.eq.Get A B i
  simp_all
  assumption


-- created on 2025-06-01
-- updated on 2025-06-26
