import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
-- given
  (A B : Matrix (Fin m) (Fin m) ℝ)
  (v : EuclideanVec m) :
-- imply
  critic_quadratic_form (A + B) v = critic_quadratic_form A v + critic_quadratic_form B v := by
-- proof
  simp [critic_quadratic_form, inner_add_right]


-- created on 2026-09-26
