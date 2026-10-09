import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c x : ℝ}
-- given
  (hxa : x ≥ a)
  (h : x ∈ Set.Icc b c) :
-- imply
  x ∈ Set.Icc (max b a) c := by
-- proof
  obtain ⟨hbx, hxc⟩ := h
  exact ⟨max_le hbx hxa, hxc⟩


-- created on 2021-04-06
