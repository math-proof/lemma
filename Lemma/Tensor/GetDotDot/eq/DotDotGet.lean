import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetDot.eq.DotGetS
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (L : Tensor α [l, m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o])
  (i : Fin l)
  (j : Fin o) :
-- imply
  ((L ⬝ᵥ M) ⬝ᵥ N)[i][j] = (L[i] ⬝ᵥ M) ⬝ᵥ Nᵀ[j] := by
-- proof
  simp [GetElem.getElem]
  erw [GetDot.eq.DotGetS.fin]
  congr 1
  erw [GetDot.eq.DotGet.fin]
  rfl


-- created on 2026-07-09
-- updated on 2026-07-21
