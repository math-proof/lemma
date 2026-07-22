import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetDot.eq.DotGetS
open Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (L : Tensor α [l, m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o])
  (i : Fin l)
  (j : Fin o) :
-- imply
  ((L @ M) @ N)[i][j] = (L[i] @ M) @ Nᵀ[j] := by
-- proof
  simp [GetElem.getElem]
  erw [GetDot.eq.DotGetS.fin]
  congr 1
  erw [GetDot.eq.DotGet.fin]
  rfl


-- created on 2026-07-09
-- updated on 2026-07-21
