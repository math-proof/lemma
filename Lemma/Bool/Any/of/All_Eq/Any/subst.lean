import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {α : Type*} [Mul α] [Add α]
  {C S : Set α}
  {a b : α}
  {f : α → α}
-- given
  (h₀ : ∀ x ∈ C, a = f x)
  (h₁ : ∃ x ∈ C, a * b + x ∈ S) :
-- imply
  ∃ x ∈ C, f x * b + x ∈ S := by
-- proof
  obtain ⟨x, hx, hxe⟩ := h₁
  rw [h₀ x hx] at hxe
  exact ⟨x, hx, hxe⟩


-- created on 2019-01-06
