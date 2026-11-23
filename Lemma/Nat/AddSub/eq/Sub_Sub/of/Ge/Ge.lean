import Lemma.Nat.EqSubAdd
import Theorem.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.EqAddSub.of.Ge
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.AddSub.eq.Sub_Sub.of.Ge.Ge |
| comm | Nat.Sub_Sub.eq.AddSub.of.Ge.Ge |
-/
@[path, comm]
private lemma main
  {a b c : ℕ}
-- given
  (h₀ : a ≥ b)
  (h₁ : b ≥ c) :
-- imply
  a - b + c = a - (b - c) := by
-- proof
  let d := b - c
  have h_b : b = d + c := by
    simp [d, h₁]
  rw [h_b] at h₀ ⊢
  rw [EqSubAdd]
  rw [Sub_Add.eq.SubSub]
  rw [EqAddSub.of.Ge]
  apply Nat.le_sub_of_add_le' h₀


-- created on 2025-06-18
-- updated on 2026-11-23
