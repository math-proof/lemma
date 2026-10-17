import sympy.Basic


@[path]
private lemma main
  {e : α} {A : Set α} [Decidable (e ∈ A)]
  {B : Set α}
-- given
  (h₀ : e ∈ B \ A) :
-- imply
  decide (e ∉ A) = true :=
-- proof
  decide_eq_true h₀.2


-- created on 2026-10-11
-- updated on 2026-10-17
