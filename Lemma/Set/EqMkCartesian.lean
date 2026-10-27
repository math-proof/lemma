import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.mk_cartesian_fst_snd_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set}
  {z: X ×ˢ Y} :
-- imply
  (mk_cartesian (fst z) (snd z)) = z  :=
-- proof
  Chapter3.SetTheory.Set.mk_cartesian_fst_snd_eq z


-- created on 2026-10-22
