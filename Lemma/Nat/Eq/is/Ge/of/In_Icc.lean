import Lemma.Nat.Eq.of.Le.Le
import Lemma.Nat.Ge.of.Eq
import Lemma.Set.Le.of.In_Icc
open Nat Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Eq.is.Ge.of.In_Icc |
| comm | Nat.Ge.is.Eq.of.In_Icc |
| mp | Nat.Ge.of.Eq.In_Icc |
| mpr | Nat.Eq.of.Ge.In_Icc |
-/
@[main, comm, mp, mpr]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h₁ : x ∈ Icc a b) :
-- imply
  x = b ↔ x ≥ b := by
-- proof
  constructor
  ·
    apply Ge.of.Eq
  ·
    intro h₀
    apply Eq.of.Le.Le (Le.of.In_Icc h₁) h₀


-- created on 2019-06-04
-- updated on 2026-08-28
