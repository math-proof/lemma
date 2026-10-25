import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_2.Part2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.ge_iff_le](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {n m:Chapter2.Nat} :
-- imply
  n ≥ m ↔ m ≤ n :=
-- proof
  by rfl


-- created on 2026-10-22
-- updated on 2026-10-23
