import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℤ}
-- given
  (h : x ∈ Finset.Ico a b) :
-- imply
  a < b := by
-- proof
  obtain ⟨ha, hb⟩ := Finset.mem_Ico.mp h
  omega


-- created on 2023-11-12
