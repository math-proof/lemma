import Mathlib
import sympy.Basic
import Instance.Analysis.Section_3_1.Part5
import Lemma.Set.IffSubsetAllIn
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Set


/--
[SetTheory.Set.subset_trans](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A B C:Chapter3.Set}
-- given
  (hAB:A ⊆ B)
  (hBC:B ⊆ C) :
-- imply
  A ⊆ C :=
-- proof
  by
    -- This proof is written to follow the structure of the original text.
    rw [IffSubsetAllIn]
    intro x hx
    rw [IffSubsetAllIn] at hAB
    apply hAB x at hx
    apply hBC x at hx
    assumption


-- created on 2026-10-22
-- updated on 2026-10-23
