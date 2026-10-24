import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
import Lemma.Nat.IffOfSNat
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Nat


/--
[SetTheory.Set.nat_coe_eq_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {m n : ℕ} :
-- imply
  (m:Object) = OfNat.ofNat n ↔ m = n :=
-- proof
  IffOfSNat (n := m) (m := n)


-- created on 2026-10-22
-- updated on 2026-10-23
