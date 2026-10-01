import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Complex.ofReal '' Set.Ioi 0) :
-- imply
  x ^ 2 ∈ Complex.ofReal '' Set.Ioi 0 := by
-- proof
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨r ^ 2, Set.mem_Ioi.mpr (pow_pos (Set.mem_Ioi.mp hr) 2), Complex.ofReal_pow r 2⟩


-- created on 2023-05-03
