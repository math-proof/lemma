import sympy.Basic


@[path]
private lemma main
  {p : Prop}
  {a b : ℝ}
  [Decidable p] :
-- imply
  sInf {(if p then a else b)} = if p then a else b := by
-- proof
  sorry


-- created on 2026-10-11
