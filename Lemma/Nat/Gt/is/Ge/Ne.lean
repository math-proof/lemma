import Lemma.Nat.Lt.is.Le.Ne
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Gt.is.Ge.Ne |
| comm | Nat.Ge.Ne.is.Gt |
| mp | Nat.Ge.Ne.of.Gt |
| mpr | Nat.Gt.of.Ge.Ne |
-/
@[main, comm, mp, mpr]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  a > b ↔ a ≥ b ∧ a ≠ b := by
-- proof
  simp [Lt.is.Le.Ne]
  grind


-- created on 2025-04-18
-- updated on 2025-11-13
