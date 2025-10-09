import Lemma.Algebra.EqSubAdd
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Algebra.GeSub.of.Ge_Add
open Algebra Nat


@[main, comm]
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
  rw [EqSubAdd.int]
  rw [Sub_Add.eq.SubSub.nat]
  rw [EqAddSub.of.Ge]
  apply GeSub.of.Ge_Add.left.nat h₀


-- created on 2025-06-18
-- updated on 2025-06-20
