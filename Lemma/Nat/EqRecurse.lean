import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_2_1
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.recurse_succ](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
@[path]
private lemma main
  {f: Chapter2.Nat → Chapter2.Nat → Chapter2.Nat}
  {c n : Chapter2.Nat} :
-- imply
  recurse f c (n++) = f n (recurse f c n) :=
-- proof
  rfl


-- created on 2026-10-22
-- updated on 2026-10-23
