import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
  {ι : Type*}
-- given
  (s : Finset ι)
  (A : ι → Matrix (Fin m) (Fin m) ℝ)
  (v : EuclideanVec m) :
-- imply
  critic_quadratic_form (∑ i ∈ s, A i) v = ∑ i ∈ s, critic_quadratic_form (A i) v := by
-- proof
  simp [critic_quadratic_form, map_sum, LinearMap.sum_apply, inner_sum]


-- created on 2026-09-26
