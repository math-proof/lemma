import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a < b) :
-- imply
  ({b, a} : Set ℝ) ⊆ Set.Icc a b := by
-- proof
  exact Set.insert_subset_iff.mpr ⟨⟨h.le, le_refl b⟩, Set.singleton_subset_iff.mpr ⟨le_refl a, h.le⟩⟩


-- created on 2026-09-27
