import Lemma.Tensor.SEqBroadcastMatmulRecS.of.SEq.SEq
open Tensor


@[main]
private lemma main
  [Mul α] [Zero α] [Add α]
  {A : Tensor α (s_A ++ [m, t])}
  {A' : Tensor α (s_A' ++ [m', t])}
  {B : Tensor α (s_B ++ [t, k])}
  {B' : Tensor α (s_B' ++ [t, k'])}
-- given
  (h_m : m = m')
  (h_k : k = k')
  (h : s_A.length = s_B.length)
  (h_A : A ≃ A')
  (h_B : B ≃ B') :
-- imply
  have h_A' : s_A = s_A' := by
    have := h_A.left
    simp [h_m] at this
    assumption
  have h_B' : s_B = s_B' := by
    have := h_B.left
    simp [h_k] at this
    assumption
  A.broadcast_matmul_rec B (by grind) ≃ A'.broadcast_matmul_rec B' (by grind) := by
-- proof
  subst h_m h_k
  apply SEqBroadcastMatmulRecS.of.SEq.SEq h h_A h_B


-- created on 2026-01-12
