import Mathlib.Topology.Algebra.InfiniteSum.Real
import sympy.Basic


@[main]
private lemma main
  {α : ℕ → ℝ}
-- given
  (h₀ : Summable fun n => α n ^ 2) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ n, α n ≤ C := by
-- proof
  refine ⟨max 1 (∑' n, α n ^ 2), le_max_of_le_left zero_le_one, fun n => ?_⟩
  if h : α n ≤ 1 then
    exact h.trans (le_max_left _ _)
  else
    calc
      _ ≤ α n ^ 2 := by nlinarith
      _ ≤ ∑' n, α n ^ 2 := h₀.le_tsum n fun _ _ => sq_nonneg _
      _ ≤ _ := le_max_right _ _


-- created on 2026-09-26