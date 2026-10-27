import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_5.Part9
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set.Fin


/--
[SetTheory.Set.Fin.toNat_mk](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_5.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n m : ℕ}
-- given
  (h: m < n) :
-- imply
  (Fin_mk n m h : ℕ) = m :=
-- proof
  Chapter3.SetTheory.Set.Fin.toNat_mk m h


-- created on 2026-10-22
