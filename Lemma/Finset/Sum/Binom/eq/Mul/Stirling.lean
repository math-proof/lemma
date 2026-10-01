import Lemma.Finset.Stirling.eq.Mul.Sum
open Finset Nat


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  ∑ i ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * (i : ℝ) ^ n = (k ! : ℝ) * (Stirling n k : ℝ) := by
-- proof
  rw [Stirling.eq.Mul.Sum]
  field_simp


-- created on 2026-09-27
