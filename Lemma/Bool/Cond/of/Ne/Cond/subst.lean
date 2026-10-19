import Lemma.Nat.Delta.eq.Ite
open Nat


@[path]
private lemma main
  [DecidableEq α]
  {x y : α}
  {p : ℕ → Prop}
-- given
  (h₀ : x ≠ y)
  (h₁ : p (KroneckerDelta x y)) :
-- imply
  p 0 := by
-- proof
  rw [Delta.eq.Ite, ite_eq_right h₀] at h₁
  apply h₁


-- created on 2020-07-18
-- updated on 2026-10-12
