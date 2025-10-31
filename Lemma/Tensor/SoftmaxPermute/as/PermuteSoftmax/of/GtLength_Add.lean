import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.Softmax.as.SoftmaxCast.of.Eq
import Lemma.Tensor.SEqPermute__0
import Lemma.Tensor.Permute.eq.Ite
import sympy.tensor.functions
open Tensor Bool


@[main]
private lemma main
  [ExpPos α]
  {i d : ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by grind⟩ d).softmax (i + d) ≃ (X.softmax i).permute ⟨i, by grind⟩ d := by
-- proof
  rw [@Tensor.Permute.eq.Ite]
  simp
  split_ifs with h_d0 h_pos? h_i0 h_i
  .
    subst h_d0
    simp
    have := Tensor.SEqPermute__0 (X.softmax i) ⟨i, by omega⟩
    apply SEq.symm ∘ SEq.trans this
    apply Tensor.Softmax.as.SoftmaxCast.of.Eq (s' := s.permute ⟨i, by grind⟩ 0) (by simp [List.EqPermute__0]) X
  .
    subst h_i0
    simp at h ⊢
    have := Tensor.SoftmaxCast.as.Softmax.of.Eq (s' := (s.permute ⟨0, by grind⟩ d)) (by simp [List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0]) (X.permuteHead (d + 1)) d
    apply SEq.trans this
    rw [@Tensor.Permute.eq.Ite]
    simp
    split_ifs
    apply SEq_Cast.of.SEq.Eq.Eq
    repeat simp [List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0]
    sorry
  .
    sorry
  .
    omega
  .
    omega


-- created on 2025-10-31
