import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {a b : ℝ} :
-- imply
  sInf {(if p then a else b)} = if p then a else b := by
-- proof
  simp [csInf_singleton]


-- created on 2026-10-11
-- updated on 2026-10-12
