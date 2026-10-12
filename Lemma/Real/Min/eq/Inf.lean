import sympy.Basic


@[path]
private lemma main
  {a b : ℝ} :
-- imply
  min a b = sInf {a, b} := by
-- proof
  simp [csInf_insert, csInf_singleton, min_def]


-- created on 2026-10-11
-- updated on 2026-10-12
