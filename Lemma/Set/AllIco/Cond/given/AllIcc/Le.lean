import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
  {g : α → Prop}
-- given
  (h₀ : g b)
  (h : ∀ k ∈ Ico a b, g k) :
-- imply
  ∀ k ∈ Icc a b, g k := by
-- proof
  intro k hk
  refine if hlt : k < b then h k ⟨hk.1, hlt⟩ else ?_
  have hkb : k = b := le_antisymm hk.2 (le_of_not_gt hlt)
  rw [hkb]
  exact h₀


-- created on 2026-10-03
