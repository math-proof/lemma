import Lemma.Complex.CeilSubDivArg.eq.Zero
open Complex


@[main]
private lemma main
-- given
  (z : ℂ)
  (n : ℕ) :
-- imply
  ⌈arg z / (2 * n * π) - 1 / 2⌉ = 0 :=
-- proof
  CeilSubDivArg.eq.Zero z n


-- created on 2018-11-05
-- updated on 2026-08-20
