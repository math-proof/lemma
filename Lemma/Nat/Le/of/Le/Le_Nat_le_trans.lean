import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_2.Part2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.le_trans](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b c:Chapter2.Nat}
-- given
  (hab: a ≤ b)
  (hbc: b ≤ c) :
-- imply
  a ≤ c :=
-- proof
  ge_trans hbc hab


-- created on 2026-10-22
-- updated on 2026-10-23
