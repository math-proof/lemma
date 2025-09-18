import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Algebra.Div.eq.CeilDiv.of.Lt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d ≤ 0) :
-- imply
  n / d = ⌈n / (d : ℚ)⌉ := by
-- proof
  by_cases h_eq : d = 0
  rw [h_eq]
  norm_num
  have := Lt.of.Le.Ne h_eq h
  apply Div.eq.CeilDiv.of.Lt_0 this


-- created on 2025-03-20
-- updated on 2025-03-30
