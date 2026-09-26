import sympy.stats.q_learning
import sympy.Basic
import Lemma.QLearningSpec.AbsSubMaxₐ.le.NormSub
import Lemma.LpSpace.NormOfLp.le.Norm.of.Ge_1


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  {spec : QLearningSpec S A} :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ z z' y, ‖spec.update z y - spec.update z' y‖ ≤ C * ‖z - z'‖ := by
-- proof
  refine ⟨|spec.γ| + 1, by positivity, fun z z' y => ?_⟩
  have e : spec.update z y - spec.update z' y = (spec.γ * (QLearningSpec.maxₐ (WithLp.ofLp z) y.2.1 - QLearningSpec.maxₐ (WithLp.ofLp z') y.2.1) - (z - z') (QLearningSpec.sa_to_fin y.1)) • QLearningSpec.x y.1 := by
    rw [QLearningSpec.update, QLearningSpec.update, ← sub_smul, PiLp.sub_apply]
    congr 1
    ring
  have hm : |QLearningSpec.maxₐ (WithLp.ofLp z) y.2.1 - QLearningSpec.maxₐ (WithLp.ofLp z') y.2.1| ≤ ‖z - z'‖ :=
    (QLearningSpec.AbsSubMaxₐ.le.NormSub _ _ _).trans (LpSpace.NormOfLp.le.Norm.of.Ge_1 (p := 2) (x := z - z') (by norm_num))
  rw [e, norm_smul, QLearningSpec.x, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  calc _ ≤ |spec.γ * (QLearningSpec.maxₐ (WithLp.ofLp z) y.2.1 - QLearningSpec.maxₐ (WithLp.ofLp z') y.2.1)| + |(z - z') (QLearningSpec.sa_to_fin y.1)| := abs_sub _ _
    _ ≤ |spec.γ| * ‖z - z'‖ + ‖z - z'‖ := by
      rw [abs_mul]
      gcongr
      exact PiLp.norm_apply_le (z - z') (QLearningSpec.sa_to_fin y.1)
    _ = _ := by ring


-- created on 2026-09-26
