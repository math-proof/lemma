import sympy.concrete.reduced
import sympy.Basic


@[path]
private lemma main
  [Fintype α]
-- given
  (v : α → ℝ) :
-- imply
  v.sum = ∑ b, v b := by
-- proof
  exact rfl


-- created on 2026-10-07
