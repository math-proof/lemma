import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
-- given
  (h : x ∈ Finset.Ico a b) :
-- imply
  x ∈ Finset.Ico a (b + 1) := by
-- proof
  obtain ⟨hax, hxb⟩ := Finset.mem_Ico.mp h
  exact Finset.mem_Ico.mpr ⟨hax, by omega⟩


-- created on 2023-08-20
