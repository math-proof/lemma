import Lemma.Tensor.LengthBatchDot.eq.Length
import Lemma.Bool.SEqUFnS.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.Eq.of.EqAppendS.EqLengthS
import sympy.tensor.Basic
open Bool List


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {X : Tensor α (bz ++ [m, k])}
  {Y : Tensor α (bz ++ [k, n])}
  {X' : Tensor α (bz' ++ [m', k'])}
  {Y' : Tensor α (bz' ++ [k', n'])}
-- given
  (h_A : X ≃ X')
  (h_B : Y ≃ Y') :
-- imply
  X.bmm Y ≃ X'.bmm Y' := by
-- proof
  have h_s := h_A.left
  have h_s' := h_B.left
  have h_bz_len : bz.length = bz'.length := by simpa using congrArg length h_s
  have h_bz := Eq.of.EqAppendS.EqLengthS h_bz_len h_s
  have h_mk := Eq.of.EqAppendS.EqLengthS.drop h_bz_len h_s
  injection h_mk with h_m h_k_tail
  injection h_k_tail with h_k
  have h_kn := Eq.of.EqAppendS.EqLengthS.drop h_bz_len h_s'
  injection h_kn with _ h_n_tail
  injection h_n_tail with h_n
  subst h_bz h_m h_k h_n
  have h_A := Eq.of.SEq h_A
  have h_B := Eq.of.SEq h_B
  subst h_A h_B
  rfl



-- created on 2026-07-04
