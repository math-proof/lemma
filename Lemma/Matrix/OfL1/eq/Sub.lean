import sympy.Basic
import sympy.stats.stochastic_process_types


@[main]
private lemma main
  {S : Type*} [Fintype S]
-- given
  (a b : S → ℝ) :
-- imply
  ofL1 (a - b) = ofL1 a - ofL1 b := by
-- proof
  ext
  simp [ofL1, sub_eq_add_neg]


-- created on 2026-09-22
