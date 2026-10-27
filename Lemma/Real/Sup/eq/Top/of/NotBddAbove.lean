import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.ExtendedReal


/--
[ExtendedReal.sup_of_unbounded](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real}
-- given
  (hb: ¬ BddAbove E) :
-- imply
  sup E = ⊤ :=
-- proof
  Chapter5.ExtendedReal.sup_of_unbounded hb


-- created on 2026-10-22
