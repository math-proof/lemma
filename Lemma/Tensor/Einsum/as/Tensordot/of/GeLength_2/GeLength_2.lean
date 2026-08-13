import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Tensor.Tensordot.of.SEq.SEq
open Bool List Tensor
set_option maxHeartbeats 1000000


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s'.length ≥ 2)
  (X : Tensor α s)
  (Y : Tensor α s') :
-- imply
  let batch_size := s.take (s.length - 2)
  let batch_size' := s'.take (s'.length - 2)
  let m := s[s.length - 2]
  let n := s[s.length - 1]
  let n' := s'[s'.length - 2]
  let k := s'[s'.length - 1]
  let X' : Tensor α (batch_size ++ [m, n]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) X
  let Y' : Tensor α (batch_size' ++ [n', k]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) Y
  let X' : Tensor α (batch_size ++ [m, n ⊔ n']) := cast (by simp) (X'.resize ⟨batch_size.length + 1, by grind⟩ (n ⊔ n'))
  let Y' : Tensor α (batch_size' ++ [n ⊔ n', k]) := cast (by simp) (Y'.resize ⟨batch_size'.length, by grind⟩ (n ⊔ n'))
  X.einsum Y ≃ (Tensor.tensordot X' Y') := by
-- proof
  unfold einsum
  apply SEq.of.Eq_Cast.Eq
  ·
    split_ifs <;> grind
  ·
    unfold Tensor.matmul_shape
    split_ifs <;> grind


-- created on 2026-07-20
-- updated on 2026-08-13
