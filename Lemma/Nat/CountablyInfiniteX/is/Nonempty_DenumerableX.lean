import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_1.Part4
open Chapter8
open Chapter8.CountablyInfinite


/--
[CountablyInfinite.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  CountablyInfinite X ↔ Nonempty (Denumerable X) :=
-- proof
  Chapter8.CountablyInfinite.iff X


-- created on 2026-10-22
