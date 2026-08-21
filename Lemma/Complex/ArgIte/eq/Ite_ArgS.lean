import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {a b : ℂ} :
-- imply
  arg (if p then a else b) = if p then arg a else arg b := by
-- proof
  split_ifs <;> rfl


-- created on 2018-11-01
-- updated on 2026-08-20
