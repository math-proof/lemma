import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.NatBitwise
open Nat


/--
[testBit_iff_mem_bitIndices](https://github.com/teorth/analysis/blob/main/Analysis/Misc/NatBitwise.lean)
-/
@[path]
private lemma main
  {n i : ℕ} :
-- imply
  n.testBit i = true ↔ i ∈ n.bitIndices :=
-- proof
  Nat.testBit_iff_mem_bitIndices n i


-- created on 2026-10-20
