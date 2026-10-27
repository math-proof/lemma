import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {θ : ℝ} :
-- imply
  Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 :=
-- proof
  Real.cos_sq_add_sin_sq θ


-- created on 2021-12-14
-- updated on 2026-10-26
