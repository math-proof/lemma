import Lemma.Bool.Imp_And.of.Imp


@[path]
private lemma main
  {a b : α}
  {l : β}
  {r : α → β}
-- given
  (h₀ : a = b)
  (h₁ : l = r a) :
-- imply
  l = r b := by
-- proof
  rw [← h₀]
  exact h₁


-- created on 2020-07-10
-- updated on 2026-11-24
