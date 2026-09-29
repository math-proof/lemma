import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e : ℤ}
  {s : Set ℤ}
  [Decidable (e ∈ s)] :
-- imply
  s ∩ {e} = if e ∈ s then {e} else ∅ := by
-- proof
  ext x
  by_cases h : e ∈ s
  · rw [if_pos h]
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun hx => hx.2, fun hx => ⟨hx ▸ h, hx⟩⟩
  · rw [if_neg h]
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro hx rfl
    exact h hx


-- created on 2026-09-27
