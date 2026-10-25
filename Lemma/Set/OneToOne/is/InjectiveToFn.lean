import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_3.Part2
import Lemma.Set.OneToOne.is.All_Eq
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.one_to_one_iff'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f: Function X Y} :
-- imply
  f.one_to_one ↔ Function.Injective f.to_fn :=
-- proof
  by
    rw [OneToOne.is.All_Eq, Function.Injective]


-- created on 2026-10-22
-- updated on 2026-10-23
