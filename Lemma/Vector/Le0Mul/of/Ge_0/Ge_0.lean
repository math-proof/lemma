import Lemma.Int.Le0Mul.of.Ge_0.Ge_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetMul.eq.MulGetS
open Int Vector


@[main]
private lemma main
  [MulZeroClass α] [Preorder α] [PosMulMono α]
  {a b : List.Vector α n}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
-- imply
  a * b ≥ 0 := by
-- proof
  intro i
  have h₀i := h₀ i
  have h₁i := h₁ i
  simp [GetElem.getElem, EqGet0_0.fin, GetMul.eq.MulGetS.fin] at h₀i h₁i ⊢
  exact Le0Mul.of.Ge_0.Ge_0 h₀i h₁i


-- created on 2026-07-27
