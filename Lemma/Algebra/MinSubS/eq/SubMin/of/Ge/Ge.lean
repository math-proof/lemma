import Lemma.Nat.EqSubAdd
import Lemma.Algebra.MinAddS.eq.AddMin
open Algebra Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h₀ : a ≥ c)
  (h₁ : b ≥ c) :
-- imply
  (a - c) ⊓ (b - c) = a ⊓ b - c := by
-- proof
  let a' := a - c
  let b' := b - c
  have h_a : a = a' + c := by
    simp [a', h₀]
  have h_b : b = b' + c := by
    simp [b', h₁]
  rw [h_a, h_b]
  rw [MinAddS.eq.AddMin]
  repeat rw [EqSubAdd]


-- created on 2025-06-20
