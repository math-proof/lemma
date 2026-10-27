import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.snd_of_mk_cartesian](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y:Chapter3.Set}
  {x:X}
  {y:Y} :
-- imply
  snd (mk_cartesian x y) = y :=
-- proof
  Chapter3.SetTheory.Set.snd_of_mk_cartesian x y


-- created on 2026-10-22
