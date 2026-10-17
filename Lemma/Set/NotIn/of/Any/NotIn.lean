import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → α}
  {S : Set α}
-- given
  (h₀ : ∃ i, x i ∉ S) :
-- imply
  ¬ ∀ i, x i ∈ S :=
-- proof
  not_forall.mpr h₀


-- created on 2026-10-11
-- updated on 2026-10-17
