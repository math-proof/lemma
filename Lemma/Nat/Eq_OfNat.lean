import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
import Lemma.Nat.EqNat
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Nat


/--
[SetTheory.Set.nat_equiv_coe_of_coe''](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {n:ℕ} :
-- imply
  ((OfNat.ofNat n:Chapter3.Nat):ℕ) = n :=
-- proof
  EqNat


-- created on 2026-10-22
-- updated on 2026-10-26
