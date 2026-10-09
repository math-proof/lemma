import Lemma.Real.LeSup.of.All_Le


@[path]
private lemma main
  {S : Set α}
  {f : α → ℝ}
  {M : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : ∀ x ∈ S, M ≥ f x) :
-- imply
  sSup (f '' S) ≤ M := by
-- proof
  exact Real.LeSup.of.All_Le h₀ fun x hx => h₁ x hx


-- created on 2019-01-18
-- updated on 2023-04-14
