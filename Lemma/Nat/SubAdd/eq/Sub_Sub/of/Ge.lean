import Lemma.Nat.EqSubAdd
import Theorem.Nat.Sub_Add.eq.SubSub
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.SubAdd.eq.Sub_Sub.of.Ge |
| comm | Nat.Sub_Sub.eq.SubAdd.of.Ge |
-/
@[path, comm]
private lemma main
  {b c : ℕ}
-- given
  (h : b ≥ c)
  (a : ℕ) :
-- imply
  a + c - b = a - (b - c) := by
-- proof
  let d := b - c
  have h_b : b = d + c := by
    simp [d, h]
  rw [h_b]
  rw [EqSubAdd]
  rw [Add.comm (a := d)]
  rw [Sub_Add.eq.SubSub]
  rw [EqSubAdd]


-- created on 2025-06-20
-- updated on 2026-11-23
