import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b c : ℤ}
-- given
  (hxa : x ≤ a)
  (h : x ∈ Finset.Ico b c) :
-- imply
  x ∈ Finset.Ico b (min c (a + 1)) := by
-- proof
  obtain ⟨hb, hc⟩ := Finset.mem_Ico.mp h
  have ha : x < a + 1 := by omega
  exact Finset.mem_Ico.mpr ⟨hb, lt_min hc ha⟩


-- created on 2023-11-12
