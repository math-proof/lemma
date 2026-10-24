import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
import Lemma.Nat.Nat.eq.Object
import Lemma.Nat.Nat.is.Eq
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Chapter3.SetTheory.Object
open Nat


/--
[SetTheory.Object.natCast_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n m:ℕ} :
-- imply
  (n : Object) = (m : Object) ↔ n = m :=
-- proof
  by
    simp [←_root_.Nat.Nat.eq.Object, Subtype.val_inj, Nat.is.Eq]


-- created on 2026-10-22
-- updated on 2026-10-23
