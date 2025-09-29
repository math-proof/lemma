import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {γ : Sort u}
  {R : α → β → Prop}
  {σ : (τ → γ) → α}
  {a b : τ → γ}
-- given
  (h₁ : R (σ b) c ∧ ¬p) :
-- imply
  R (σ fun x => (if p then
    a x
  else
    b x)) c ∧ ¬p := by
-- proof
  simp_all


-- created on 2025-07-29
