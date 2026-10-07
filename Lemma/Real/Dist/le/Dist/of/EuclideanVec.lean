import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {d : ℕ}
-- given
  (r : ℝ)
  (θ θ' : EuclideanVec d) :
-- imply
  dist (actor_box_projection r θ) (actor_box_projection r θ') ≤ dist θ θ' := by
-- proof
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
  simp only [actor_box_projection, PiLp.toLp_apply, Real.dist_eq]
  apply pow_le_pow_left₀ (abs_nonneg _) _ 2
  calc
    _ = |max (min r (θ j)) (-r) - max (min r (θ' j)) (-r)| := by rw [max_comm (-r), max_comm (-r)]
    _ ≤ |min r (θ j) - min r (θ' j)| := abs_max_sub_max_le_abs _ _ _
    _ ≤ max |r - r| |θ j - θ' j| := abs_min_sub_min_le_max _ _ _ _
    _ = |θ j - θ' j| := by simp


-- created on 2026-09-26
