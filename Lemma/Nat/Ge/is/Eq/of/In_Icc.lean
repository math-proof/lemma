import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [PartialOrder α]
  {a b x : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  b ≤ x ↔ x = b := by
-- proof
  refine ⟨fun hge => le_antisymm h.right hge, fun heq => heq ▸ le_rfl⟩


-- created on 2026-10-03
