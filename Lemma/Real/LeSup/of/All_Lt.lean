import Lemma.Real.LeSup.of.All_Le


@[main]
private lemma main
  {S : Set α}
  {f : α → ℝ}
  {M : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : ∀ x ∈ S, f x < M) :
-- imply
  sSup (f '' S) ≤ M := by
-- proof
  exact Real.LeSup.of.All_Le h₀ fun x hx => le_of_lt (h₁ x hx)


-- created on 2019-01-28
