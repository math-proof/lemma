import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_2_1
import Lemma.Nat.All.of.All_Nat_induction
import Lemma.Nat.EqRecurse
import Lemma.Nat.EqRecurseNat0
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.eq_recurse](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
@[path]
private lemma main
  {f: Chapter2.Nat → Chapter2.Nat → Chapter2.Nat}
  {c: Chapter2.Nat}
  {a: Chapter2.Nat → Chapter2.Nat} :
-- imply
  (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c :=
-- proof
  by
    constructor
    ·
      intro ⟨h0, hsucc⟩
      apply funext
      apply All.of.All_Nat_induction
      · exact h0
      intro n hn
      rw [hsucc n, EqRecurse, hn]
    intro h
    rw [h]
    constructor
    · exact EqRecurseNat0
    exact fun n ↦ EqRecurse


-- created on 2026-10-22
-- updated on 2026-10-26
