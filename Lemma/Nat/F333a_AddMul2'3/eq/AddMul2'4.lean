import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_3_3_fn
import Lemma.Nat.F333aNat.eq.Add_1
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Set
open Nat


/--
[SetTheory.Set.f_3_3_3a_eval'''](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ} :
-- imply
  f_3_3_3a (2*n+3: ℕ) = (2*n+4:ℕ) :=
-- proof
  by
    convert F333aNat.eq.Add_1


-- created on 2026-10-22
-- updated on 2026-10-23
