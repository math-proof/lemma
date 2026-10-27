import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_3_inv
import Lemma.Set.Eq_GetInverse.is.Eq.of.Bijective
import Lemma.Set.Bijective.is.BijectiveToFn
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.inverse_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set} [Nonempty X]
  {f: Function X Y}
-- given
  (h: f.bijective) :
-- imply
  (f.inverse h).to_fn = Function.invFun f.to_fn :=
-- proof
  by
    ext y; congr; symm
    rw [Eq_GetInverse.is.Eq.of.Bijective]
    apply Function.rightInverse_invFun (Bijective.is.BijectiveToFn (f := f)).mp h |>.2


-- created on 2026-10-22
-- updated on 2026-10-26
