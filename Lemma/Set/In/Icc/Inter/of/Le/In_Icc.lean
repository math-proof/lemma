import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c x : ℝ}
-- given
  (hxa : x ≤ a)
  (h : x ∈ Set.Icc b c) :
-- imply
  x ∈ Set.Icc b (min c a) := by
-- proof
  obtain ⟨hbx, hxc⟩ := h
  exact ⟨hbx, le_min hxc hxa⟩


-- created on 2020-11-27
