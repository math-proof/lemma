import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_2_1
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.recurse_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
@[path]
private lemma main
  {f: Chapter2.Nat → Chapter2.Nat → Chapter2.Nat}
  {c: Chapter2.Nat} :
-- imply
  Chapter2.Nat.recurse f c 0 = c :=
-- proof
  rfl


-- created on 2026-10-22
-- updated on 2026-10-26
