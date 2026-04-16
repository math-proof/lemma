import Lemma.List.Prod.eq.Mul_ProdDropLast.of.GtLength_0
import Lemma.Nat.EqDivS.of.Eq
open List Nat


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s[s.length - 1] > 0) :
-- imply
  s.dropLast.prod = s.prod / s[s.length - 1] := by
-- proof
  have h_prod := Prod.eq.Mul_ProdDropLast.of.GtLength_0 h₀
  have h_div := EqDivS.of.Eq h_prod s[s.length - 1]
  simp [h₁] at h_div
  exact h_div.symm


-- created on 2026-04-16
