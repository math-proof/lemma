import Lemma.Tensor.Tensordot.as.Matmul.of.GeLengthS
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
import Lemma.Tensor.SEqReshapeS.of.Eq.Eq.Dvd
open Tensor


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s : List ℕ}
-- given
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α [n, k]) :
-- imply
  (X.tensordot Y : Tensor α (broadcast_shape s [] ++ [m, k])) ≃ X.matmul (Y.reshape (s ++ [n, k]) (by simp)) (by grind) := by
-- proof
  have := Tensordot.as.Matmul.of.GeLengthS (by simp) X Y (s' := [])
  apply this.trans
  apply SEqMatmulS.of.SEq.SEq
  ·
    simp
  ·
    rfl
  ·
    apply SEqReshapeS.of.Eq.Eq.Dvd
    ·
      simp
    ·
      rfl


-- created on 2026-01-12
