import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (ha : 0 ≤ a)
  (h : x ∈ Set.Ico a b) :
-- imply
  Real.sqrt x ∈ Set.Ico (Real.sqrt a) (Real.sqrt b) := by
-- proof
  exact Set.mem_Ico.mpr ⟨Real.sqrt_le_sqrt h.1, Real.sqrt_lt_sqrt (ha.trans h.1) h.2⟩


-- created on 2019-06-28
