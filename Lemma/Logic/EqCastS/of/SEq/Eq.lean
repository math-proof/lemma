import stdlib.SEq
import Lemma.Basic


@[main]
private lemma left
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h₀ : n_a = n)
  (h₁ : a ≃ b) :
-- imply
  have h_a : Vector n_a = Vector n := by rw [h₀]
  have h_b : Vector n_b = Vector n := by rwa [← h₁.left]
  cast h_a a = cast h_b b := by
-- proof
  let ⟨h_n, h₁⟩ := h₁
  subst h_n
  have h₁ := HEq.eq h₁
  simp_all


@[main]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h₀ : n_b = n)
  (h₁ : a ≃ b) :
-- imply
  have h_a : Vector n_a = Vector n := by rw [h₁.left, h₀]
  have h_b : Vector n_b = Vector n := by rw [h₀]
  cast h_a a = cast h_b b := by
-- proof
  apply left _ h₁
  rw [h₁.left, h₀]


-- created on 2025-05-30
-- updated on 2025-06-01
