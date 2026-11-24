import Lemma.Bool.Imp_And.of.Imp


@[path]
private lemma main
  {a b : α}
  {l : α → β}
  {r : β}
-- given
  (h₀ : a = b)
  (h₁ : l a = r) :
-- imply
  l b = r := by
-- proof
  rw [← h₀]
  exact h₁




-- created on 2018-01-09
-- updated on 2026-11-24
