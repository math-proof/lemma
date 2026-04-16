import Lemma.List.Prod.eq.Mul_ProdTail.of.NeLength_0
import Lemma.Nat.EqDivS.of.Eq
open List Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h₀: s.length ≠ 0)
  (h₁: s[0] ≠ 0) :
-- imply
  s.tail.prod = s.prod / s[0] := by
-- proof
  have h_prod := Prod.eq.Mul_ProdTail.of.NeLength_0 h₀
  have h_div := EqDivS.of.Eq h_prod s[0]
  simp [h₁] at h_div
  exact h_div.symm


-- created on 2024-07-01
