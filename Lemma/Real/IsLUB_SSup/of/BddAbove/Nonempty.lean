import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.ExtendedReal


/--
[ExtendedReal.sSup_of_bounded](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real}
-- given
  (hnon: E.Nonempty)
  (hb: BddAbove E) :
-- imply
  IsLUB E (sSup E) :=
-- proof
  Chapter5.ExtendedReal.sSup_of_bounded hnon hb


-- created on 2026-10-22
