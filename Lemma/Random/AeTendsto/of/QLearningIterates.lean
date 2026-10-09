import sympy.stats.q_learning
import sympy.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Lemma.LpSpace.MeasurableHalfSq.of.Ge_1
import Lemma.LpSpace.MeasurableHalfSq'.of.Ge_1
import Lemma.Random.MeasurableUncurryUpdateTarget
import Lemma.Random.Any_Ge_0AndAll_All_LeNormSubUpdateTarget_MulNormSub
import Lemma.Random.ExpectedUpdateTarget.eq.Sum_Sum_SMul
import Lemma.Random.ExpectedUpdateTargetOptimalQ.eq.OptimalQ
import Lemma.Random.LyapunovFunctionHalfSq
import Lemma.Random.AeTendsto.of.LyapunovFunction.Measurable.Measurable.All_Eq_Sum_Sum_SMul.Eq.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.MeasurableUncurry.IteratesOfResidual
open Filter Topology


@[path]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A} [RobbinsMonro spec.α]
  {q : ℕ → (ℕ → (S × A) × (S × A)) → EuclideanVec (Fintype.card (S × A))}
-- given
  (h : QLearningIterates spec q) :
-- imply
  ∀ᵐ ω ∂spec.MRP.iid_samples, Tendsto (fun n => q n ω) atTop (𝓝 spec.optimal_q) := by
-- proof
  have h2p : 2 ≤ spec.pmin := le_max_left _ _
  exact Random.AeTendsto.of.LyapunovFunction.Measurable.Measurable.All_Eq_Sum_Sum_SMul.Eq.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.MeasurableUncurry.IteratesOfResidual (MRP := spec.MRP)
    ⟨h.init, fun n ω => by rw [h.step, QLearningSpec.update_target, add_sub_cancel_right]⟩
    Random.MeasurableUncurryUpdateTarget Random.Any_Ge_0AndAll_All_LeNormSubUpdateTarget_MulNormSub
    Random.ExpectedUpdateTargetOptimalQ.eq.OptimalQ.symm Random.ExpectedUpdateTarget.eq.Sum_Sum_SMul
    ((LpSpace.MeasurableHalfSq.of.Ge_1 (by omega)).comp ((WithLp.measurable_toLp _ _).comp (WithLp.measurable_ofLp _ _)))
    (((WithLp.measurable_toLp _ _).comp (WithLp.measurable_ofLp _ _)).comp ((LpSpace.MeasurableHalfSq'.of.Ge_1 (by omega)).comp ((WithLp.measurable_toLp _ _).comp (WithLp.measurable_ofLp _ _))))
    Random.LyapunovFunctionHalfSq


-- created on 2026-09-26
