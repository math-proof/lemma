import sympy.stats.q_learning
import sympy.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Lemma.LpSpace.MeasurableHalfSq.of.Ge_1
import Lemma.LpSpace.MeasurableHalfSq'.of.Ge_1
import Lemma.QLearningSpec.MeasurableUncurryUpdateTarget
import Lemma.QLearningSpec.Any_Ge_0AndAll_All_LeNormSubUpdateTarget_MulNormSub
import Lemma.QLearningSpec.ExpectedUpdateTarget.eq.Sum_Sum_SMul
import Lemma.QLearningSpec.ExpectedUpdateTargetOptimalQ.eq.OptimalQ
import Lemma.QLearningSpec.LyapunovFunctionHalfSq
import Lemma.Iterates.AeTendsto.of.LyapunovFunction.Measurable.Measurable.All_Eq_Sum_Sum_SMul.Eq.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.MeasurableUncurry.IteratesOfResidual.Lt_1.Gt_Div2'3
open Filter Topology


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A}
  {q : ℕ → (ℕ → (S × A) × (S × A)) → EuclideanVec (Fintype.card (S × A))}
  {ν : ℝ}
-- given
  (h₀ : 2 / 3 < ν)
  (h₁ : ν < 1)
  (h₂ : QLearningIterates spec q)
  (h₃ : spec.α = fun n : ℕ => inv_poly ν 2 n) :
-- imply
  ∀ᵐ ω ∂spec.MRP.markov_samples, Tendsto (fun n => q n ω) atTop (𝓝 spec.optimal_q) := by
-- proof
  have h2p : 2 ≤ spec.pmin := le_max_left _ _
  exact Iterates.AeTendsto.of.LyapunovFunction.Measurable.Measurable.All_Eq_Sum_Sum_SMul.Eq.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.MeasurableUncurry.IteratesOfResidual.Lt_1.Gt_Div2'3 (MRP := spec.MRP) h₀ h₁
    ⟨h₂.init, fun n ω => by rw [h₂.step, h₃, QLearningSpec.update_target, add_sub_cancel_right]⟩
    QLearningSpec.MeasurableUncurryUpdateTarget QLearningSpec.Any_Ge_0AndAll_All_LeNormSubUpdateTarget_MulNormSub
    QLearningSpec.ExpectedUpdateTargetOptimalQ.eq.OptimalQ.symm QLearningSpec.ExpectedUpdateTarget.eq.Sum_Sum_SMul
    ((LpSpace.MeasurableHalfSq.of.Ge_1 (by omega)).comp ((WithLp.measurable_toLp _ _).comp (WithLp.measurable_ofLp _ _)))
    (((WithLp.measurable_toLp _ _).comp (WithLp.measurable_ofLp _ _)).comp ((LpSpace.MeasurableHalfSq'.of.Ge_1 (by omega)).comp ((WithLp.measurable_toLp _ _).comp (WithLp.measurable_ofLp _ _))))
    QLearningSpec.LyapunovFunctionHalfSq


-- created on 2026-09-26
