import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
  {s : List α}
  {x₀ : α}
-- given
  (h: ∀ x ∈ s, x = x₀) :
-- imply
  s is constant := by
-- proof
  match s with
  | .nil =>
    simp [IsConstant.is_constant]
  | .cons x s =>
    simp at h
    intro t t_in_s
    have h₀ : x = x₀ := h.left
    have h₁ : ∀ a ∈ s, a = x₀ := h.right
    have h₂ : t = x₀ := h₁ t t_in_s
    rw [h₀, h₂]


-- created on 2024-07-01
