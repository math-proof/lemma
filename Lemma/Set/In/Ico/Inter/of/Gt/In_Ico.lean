import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b c : ℤ}
-- given
  (hgt : x > c)
  (h : x ∈ Finset.Ico a b) :
-- imply
  x ∈ Finset.Ico (max a (c + 1)) b := by
-- proof
  obtain ⟨ha, hb⟩ := Finset.mem_Ico.mp h
  have hc : c + 1 ≤ x := Int.add_one_le_iff.mpr hgt
  exact Finset.mem_Ico.mpr ⟨max_le ha hc, hb⟩


-- created on 2023-11-12
