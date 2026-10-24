import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_3
import Lemma.Nat.EqRecurseNat0
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.zero_pow_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  (0:Chapter2.Nat) ^ 0 = 1 :=
-- proof
  EqRecurseNat0 (f := fun _ prod ↦ prod * 0)


-- created on 2026-10-22
-- updated on 2026-10-23
