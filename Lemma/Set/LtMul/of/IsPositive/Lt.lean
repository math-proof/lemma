import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : x ∈ Set.Ioi 0)
  (h₁ : a < b) :
-- imply
  a * x < b * x := by
-- proof
  rw [Set.mem_Ioi] at h₀
  exact mul_lt_mul_of_pos_right h₁ h₀


-- created on 2023-10-15
-- updated on 2026-10-26
