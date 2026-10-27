import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory


/--
[SetTheory.Set.mem_iProd](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {I: Chapter3.Set}
  {X: I → Chapter3.Set}
  {t:Object} :
-- imply
  t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x :=
-- proof
  Chapter3.SetTheory.Set.mem_iProd t


-- created on 2026-10-22
