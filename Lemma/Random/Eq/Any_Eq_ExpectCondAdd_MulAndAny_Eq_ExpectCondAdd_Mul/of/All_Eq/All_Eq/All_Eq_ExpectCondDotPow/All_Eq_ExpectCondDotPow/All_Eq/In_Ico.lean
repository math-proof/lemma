import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Initialize.Tactic.Attr.Basic


/--
One-state Bellman backup: if every action value is the reward plus a discounted constant continuation,
the optimal value is the supremum of those backups.
-/
@[path]
private lemma main
  {Q r : ι → ℝ}
  {γ V : ℝ}
-- given
  (h₀ : ∀ a, Q a = r a + γ * V) :
-- imply
  (⨆ a, Q a) = ⨆ a, r a + γ * V ∧ ∀ a, Q a = r a + γ * V := by
-- proof
  refine ⟨?_, h₀⟩
  simp_rw [h₀]


-- created on 2023-04-26
-- updated on 2026-10-26
