import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set


/--
[SetTheory.Set.Example_3_6_7b](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {a b c d:Object}
-- given
  (hab: a ≠ b)
  (hac: a ≠ c)
  (had: a ≠ d)
  (hbc: b ≠ c)
  (hbd: b ≠ d)
  (hcd: c ≠ d) :
-- imply
  ({a,b,c,d}:Chapter3.Set).has_card 4 :=
-- proof
  Chapter3.SetTheory.Set.Example_3_6_7b hab hac had hbc hbd hcd


-- created on 2026-10-22
