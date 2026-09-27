import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  {a b M : ℝ}
  {f : ℝ → ℝ}
-- given
  (hab : a < b)
  (hbdd : BddAbove (f '' Set.Ioo a b))
  (h : M = sSup (f '' Set.Ioo a b)) :
-- imply
  ∀ x ∈ Set.Ioo a b, M ≥ f x := by
-- proof
  intro x hx
  apply (csSup_le_iff hbdd ((Set.nonempty_Ioo.mpr hab).image f)).mp h.symm.le
  exact Set.mem_image_of_mem f hx


-- created on 2026-09-26
