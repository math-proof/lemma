import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_3_6.Part5
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set hiding Fin


/--
[SetTheory.Set.card_fin_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_6.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ} :
-- imply
  (Chapter3.SetTheory.Set.Fin n).has_card n :=
-- proof
  Chapter3.SetTheory.Set.card_fin_eq n


-- created on 2026-10-22
