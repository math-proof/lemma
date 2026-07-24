import Lemma.Bool.SEq.is.Eq
import Lemma.List.Eq.of.EqLengthS.EqAppendS
import Lemma.Tensor.Tensordot.of.SEq.SEq
open Bool List Tensor


@[main]
private lemma main
  [Mul α] [Zero α] [Add α]
  {A : Tensor α (s_A ++ [m, n])}
  {A' : Tensor α (s_A' ++ [m', n'])}
  {B : Tensor α (s_B ++ [n, k])}
  {B' : Tensor α (s_B' ++ [n', k'])}
-- given
  (h_m : m = m')
  (h_k : k = k')
  (h_A : A ≃ A')
  (h_B : B ≃ B') :
-- imply
  A.tensordot B ≃ A'.tensordot B' := by
-- proof
  subst h_m h_k
  have h_sA := Eq.of.EqLengthS.EqAppendS h_A.left (by grind)
  subst h_sA
  have h_sB := Eq.of.EqLengthS.EqAppendS h_B.left (by grind)
  subst h_sB
  apply SEq.of.Eq
  apply Tensordot.of.SEq.SEq h_A h_B


-- created on 2026-07-20
