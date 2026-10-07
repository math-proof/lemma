import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
-- given
  (u v : EuclideanVec m) :
-- imply
  critic_quadratic_form (Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u)) v = inner ℝ u v ^ 2 := by
-- proof
  have hA : ∀ x : EuclideanVec m, Matrix.toEuclideanLin (Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u)) x = WithLp.toLp 2 (Matrix.mulVec (Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u)) (WithLp.ofLp x)) := fun x => rfl
  simp only [critic_quadratic_form, hA, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, pow_two, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


-- created on 2026-09-26
