import Mathlib
import sympy.Basic
import sympy.analysis.Misc.NatBitwise
open Nat


/--
[testBit_finset_sum_pow_two](https://github.com/teorth/analysis/blob/main/Analysis/Misc/NatBitwise.lean)
-/
@[path]
private lemma main
  {s : Finset ℕ}
  {i : ℕ} :
-- imply
  (s.sum (2^·)).testBit i = true ↔ i ∈ s :=
-- proof
  Nat.testBit_finset_sum_pow_two


-- created on 2026-10-20
