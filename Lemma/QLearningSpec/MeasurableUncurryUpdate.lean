import sympy.stats.q_learning
import sympy.Basic
import Lemma.QLearningSpec.AbsSubMaxₐ.le.NormSub


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  {spec : QLearningSpec S A} :
-- imply
  Measurable (Function.uncurry spec.update) := by
-- proof
  have hmax : ∀ s, Continuous fun q : EuclideanVec (Fintype.card (S × A)) => QLearningSpec.maxₐ (WithLp.ofLp q) s := fun s =>
    (LipschitzWith.of_dist_le_mul (K := 1) (f := fun q : Fin (Fintype.card (S × A)) → ℝ => QLearningSpec.maxₐ q s) fun q q' => by simpa [Real.dist_eq, dist_eq_norm] using QLearningSpec.AbsSubMaxₐ.le.NormSub q q' s).continuous.comp (PiLp.continuous_ofLp 2 _)
  refine measurable_from_prod_countable_left fun y => Continuous.measurable ?_
  simp only [Function.uncurry_apply_pair, QLearningSpec.update]
  exact ((continuous_const.add (continuous_const.mul (hmax y.2.1))).sub (PiLp.continuous_apply 2 _ _)).smul continuous_const


-- created on 2026-09-26
