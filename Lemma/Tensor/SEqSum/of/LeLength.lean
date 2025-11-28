import sympy.tensor.tensor
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Nat.NotGe.of.Lt
open List Bool Nat


@[main, comm]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  X.sum d ≃ X := by
-- proof
  unfold Tensor.sum
  split_ifs with h
  ·
    have h := NotGe.of.Lt h
    contradiction
  ·
    apply SEqCast.of.Eq
    rwa [EqEraseIdx.of.LeLength]


-- created on 2025-06-23
-- updated on 2025-09-20
