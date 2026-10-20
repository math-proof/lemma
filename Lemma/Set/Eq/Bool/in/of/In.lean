import sympy.Basic


@[path]
private lemma main
  {e : α} {s : Set α} [Decidable (e ∈ s)]
-- given
  (h₀ : e ∈ s) :
-- imply
  decide (e ∈ s) = true :=
-- proof
  decide_eq_true h₀


-- created on 2020-11-03
-- updated on 2026-10-17
