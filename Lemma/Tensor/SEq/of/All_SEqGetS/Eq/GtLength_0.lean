import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Ne_Nil
import sympy.tensor.tensor
open Tensor List


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
  have h_length := Length.eq.Get_0.of.GtLength_0 h_s A
  have h_s := Ne_Nil.of.GtLength_0 h_s
  apply SEq.of.All_SEqGetS.Eq.Ne_Nil h_s h
  intro i
  simp at i
  exact h_all ⟨i.val, by simp [← h_length]⟩



-- created on 2025-11-01
-- updated on 2025-11-06
