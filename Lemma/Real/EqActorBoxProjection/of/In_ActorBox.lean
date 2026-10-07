import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {d : ℕ}
  {r : ℝ}
  {θ : EuclideanVec d}
-- given
  (h₀ : θ ∈ actor_box d r) :
-- imply
  actor_box_projection r θ = θ := by
-- proof
  ext j
  have := abs_le.1 (h₀ j)
  simp [actor_box_projection, min_eq_right this.2, max_eq_right this.1]


-- created on 2026-09-26
