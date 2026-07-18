import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
-- this is added to avoid a bug in the Lean 4 compiler that environment saying: already contains 'List.getElem?_zipWith.match_1.congr_eq_1._sparseCasesOn_2'
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
open Tensor Nat


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ s'.length)
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α (s' ++ [n', k']))
  (i : Fin n) :
-- imply
  i < (X @ Y).length := by
-- proof
  match s, s' with
  | [], []
  | _ :: _, [] =>
    rw [Length.eq.Get_0.of.GtLength_0 (by simp [matmul_shape])]
    simp [matmul_shape, broadcast_shape]
  | sₐ :: sₜ, s'ₐ :: s'ₜ =>
    rw [Length.eq.Get_0.of.GtLength_0 (by simp [matmul_shape, broadcast_shape])]
    simp [matmul_shape, broadcast_shape]
    grind


-- created on 2026-07-16
