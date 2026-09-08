import sympy.Basic


@[main]
private lemma main
  [Zero α] [One α] [NeZero (1 : α)]
  {x y : α}
-- given
  (h : ({x, y} : Set α) = {0, 1}) :
-- imply
  x ≠ y := by
-- proof
  intro hxy
  have h := hxy ▸ h
  simp at h
  have h0 : (0 : α) = y := by
    have : (0 : α) ∈ ({0, 1} : Set α) := by simp
    rw [← h] at this
    simpa using this
  have h1 : (1 : α) = y := by
    have : (1 : α) ∈ ({0, 1} : Set α) := by simp
    rw [← h] at this
    simpa using this
  exact zero_ne_one (h0.trans h1.symm)


-- created on 2020-08-27
-- updated on 2026-09-08
