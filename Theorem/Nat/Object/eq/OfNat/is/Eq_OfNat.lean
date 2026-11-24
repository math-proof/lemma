module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_3_1.Part5
public import Theorem.Nat.EqNat
public import Theorem.Nat.Eq_Nat
public import Theorem.Nat.Nat.eq.Object
public import Theorem.Nat.OfNat.eq.Object

public section

open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Nat


/--
[SetTheory.Set.nat_coe_eq_iff'](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private theorem main
  [SetTheory]
  {m: Chapter3.Nat}
  {n : ℕ} :
-- imply
  (m:Object) = (OfNat.ofNat n:Object) ↔ (m:ℕ) = OfNat.ofNat n :=
-- proof
  by
    constructor
    ·
      intro h
      rw [_root_.Nat.OfNat.eq.Object] at h
      have hm : m = (n : Chapter3.Nat) := by
        apply Subtype.ext
        simpa [_root_.Nat.Nat.eq.Object] using h
      have hmn : (m : ℕ) = n := by
        simpa [hm] using EqNat
      rw [hmn]
      show n = n
      rfl
    ·
      intro h
      have hm : m = (n : Chapter3.Nat) := by
        have : m = ((m : ℕ) : Chapter3.Nat) := Eq_Nat.symm
        rw [this, h]
        rfl
      simpa [hm, _root_.Nat.Nat.eq.Object] using _root_.Nat.OfNat.eq.Object.symm


-- created on 2026-10-22
-- updated on 2026-10-26
