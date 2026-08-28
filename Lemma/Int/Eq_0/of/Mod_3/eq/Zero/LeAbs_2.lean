import Lemma.Int.LeAbs.is.LeNeg.Le
open Int


@[main]
private lemma main
  {d : ℤ}
-- given
  (h₀ : |d| ≤ 2)
  (h₁ : d % 3 = 0) :
-- imply
  d = 0 := by
-- proof
  obtain ⟨hlo, hhi⟩ := LeNeg.Le.of.LeAbs h₀
  omega


-- created on 2026-08-28
