import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_2_1
import Lemma.Nat.EqRecurseNat0
import Lemma.Nat.EqRecurse
import Lemma.Nat.EqAndAll_Eq.is.Eq_Recurse
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.recurse_uniq](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
@[path]
private lemma main
  {f: Chapter2.Nat → Chapter2.Nat → Chapter2.Nat}
  {c: Chapter2.Nat} :
-- imply
  ∃! (a: Chapter2.Nat → Chapter2.Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) :=
-- proof
  by
    apply ExistsUnique.intro (recurse f c)
    ·
      constructor
      · exact EqRecurseNat0
      exact fun n ↦ EqRecurse
    intro a
    exact EqAndAll_Eq.is.Eq_Recurse.mp


-- created on 2026-10-22
-- updated on 2026-10-23
