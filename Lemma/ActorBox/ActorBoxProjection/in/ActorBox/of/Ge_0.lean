import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {d : ℕ}
  {r : ℝ}
-- given
  (h₀ : 0 ≤ r)
  (θ : EuclideanVec d) :
-- imply
  actor_box_projection r θ ∈ actor_box d r := by
-- proof
  intro j
  simp only [actor_box_projection, PiLp.toLp_apply]
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩


-- created on 2026-09-26
