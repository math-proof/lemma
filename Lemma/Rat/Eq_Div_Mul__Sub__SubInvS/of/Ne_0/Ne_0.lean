import Lemma.Rat.Div1.eq.Inv
import Lemma.Rat.SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0
open Rat


@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
-- proof
  rw [
    ← Div1.eq.Inv,
    ← Div1.eq.Inv,
    SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0 h₀ h₁
  ]
  simp


-- created on 2024-07-01
