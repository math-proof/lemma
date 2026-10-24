import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.add_le_add_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a b c:Chapter2.Nat} :
-- imply
  a ≤ b ↔ a + c ≤ b + c :=
-- proof
  add_ge_add_right b a c


-- created on 2026-10-22
-- updated on 2026-10-23
