import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
-- given
  (v : EuclideanVec m) :
-- imply
  critic_quadratic_form 1 v = ‖v‖ ^ 2 := by
-- proof
  simp [critic_quadratic_form]


-- created on 2026-09-26
