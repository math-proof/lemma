import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open Tensor Nat


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s ≠ [])
  (h_len : s'.length ≤ s.length)
  (X : Tensor α (n :: s))
  (Y : Tensor α (n' :: s'))
  (i : Fin n) :
-- imply
  i < (X @ Y).length := by
-- proof
  if h_s' : s'.length > 0 then
    obtain h_len | h_len := Lt.ou.Eq.of.Le h_len
    ·
      rw [Length.eq.Get_0.of.GtLength_0] <;>
      ·
        simp [matmul_shape, broadcast_shape]
        grind
    ·
      by_cases h_n : n' < n <;>
      ·
        rw [Length.eq.Get_0.of.GtLength_0] <;>
        ·
          simp [matmul_shape, broadcast_shape]
          grind
  else
    rw [Length.eq.Get_0.of.GtLength_0] <;>
    ·
      simp [matmul_shape, broadcast_shape]
      grind


-- created on 2026-01-04
