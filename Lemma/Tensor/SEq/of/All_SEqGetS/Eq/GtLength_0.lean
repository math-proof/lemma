import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq
import stdlib.SEq
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s.length > 0)
  (h : s = s')
  (h_all : ∀ i : Fin s[0], A.get ⟨i, by simp [Tensor.Length.eq.Get_0.of.GtLength_0 h_s]⟩ ≃ B.get ⟨i, by simp [Tensor.Length.eq.Get_0.of.GtLength_0 (h ▸ h_s)]; aesop⟩) :
-- imply
  A ≃ B := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    match s' with
    | [] =>
      contradiction
    | s'₀ :: s' =>
      injection h with h₀ h_s
      subst h₀
      apply SEq.of.All_SEqGetS.Eq h_s
      intro i
      exact h_all i


-- created on 2025-11-01
