import sympy.tensor.tensor
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Tensor.Length.of.Eq
import Lemma.List.EqConsS.is.Eq.Eq
open Tensor List


@[main]
private lemma main
  {A : Tensor α s_A}
  {B : Tensor α s_B}
-- given
  (h : s_A ≠ [])
  (h₀ : s_A = s_B)
  (h₁ : ∀ i : Fin A.length, A.get i ≃ B.get ⟨i, by simp [Length.of.Eq h₀.symm B A]⟩) :
-- imply
  A ≃ B := by
-- proof
  match s_A, s_B with
  | [], [] =>
    constructor <;>
    ·
      aesop
  | [], s_B₀ :: s_B =>
    simp_all
  | s_A₀ :: s_A, [] =>
    simp_all
  | s_A₀ :: s_A, s_B₀ :: s_B =>
    have ⟨h₀, h⟩ := Eq.Eq.of.EqConsS h₀
    apply SEq.of.All_SEqGetS.Eq.Eq (by assumption) (by assumption)
    assumption


-- created on 2025-10-10
