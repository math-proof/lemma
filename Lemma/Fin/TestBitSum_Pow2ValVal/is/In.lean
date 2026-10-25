import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.NatBitwise
open Nat


/--
[testBit_sum_pow_two_fin](https://github.com/teorth/analysis/blob/main/Analysis/Misc/NatBitwise.lean)
-/
@[path]
private lemma main
  {k : ℕ}
  {s : Finset (Fin k)}
  {j : Fin k} :
-- imply
  (s.sum fun i => (2:ℕ)^i.val).testBit j.val ↔ j ∈ s :=
-- proof
  Nat.testBit_sum_pow_two_fin j


-- created on 2026-10-20
