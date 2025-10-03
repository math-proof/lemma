import Lemma.List.Prod.eq.Mul_ProdTail.of.Ne_0.NeLength_0
import Lemma.Algebra.EqDivS.of.Eq
open Algebra List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h₀: s.length ≠ 0)
  (h₁: s[0] ≠ 0) :
-- imply
  s.tail.prod = s.prod / s[0] := by
-- proof
  -- Use the product property
  have h_prod := Prod.eq.Mul_ProdTail.of.Ne_0.NeLength_0 h₀ h₁
  -- divide both sides by s[0]
  have h_div := EqDivS.of.Eq h_prod s[0]
  simp [h₁] at h_div
  -- h_div : s.prod / s[0] = s.tail.prod
  exact h_div.symm


-- created on 2024-07-01
