import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Finset


/--
[Finset.Icc_eq_cast](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {N:ℕ} :
-- imply
  Icc 0 (N:ℤ) = map Nat.castEmbedding (.Icc 0 N) :=
-- proof
  Chapter8.Finset.Icc_eq_cast N


-- created on 2026-10-22
