import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x : Fin n → ℂ} :
-- imply
  √(∑ i, ‖x i‖ ^ 2) = √(∑ i, ‖~(x i)‖ ^ 2) := by
-- proof
  simp only [Complex.conj, Complex.norm_conj]


-- created on 2023-06-24
