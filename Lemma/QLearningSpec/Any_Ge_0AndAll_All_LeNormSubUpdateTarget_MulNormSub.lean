import sympy.stats.q_learning
import sympy.Basic
import Lemma.QLearningSpec.Any_Ge_0AndAll_All_LeNormSubUpdate_MulNormSub


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  {spec : QLearningSpec S A} :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ z z' y, ‖spec.update_target z y - spec.update_target z' y‖ ≤ C * ‖z - z'‖ := by
-- proof
  obtain ⟨C, hC, h⟩ := QLearningSpec.Any_Ge_0AndAll_All_LeNormSubUpdate_MulNormSub (spec := spec)
  refine ⟨C + 1, by positivity, fun z z' y => ?_⟩
  calc _ = ‖(spec.update z y - spec.update z' y) + (z - z')‖ := by rw [QLearningSpec.update_target, QLearningSpec.update_target, add_sub_add_comm]
    _ ≤ _ := norm_add_le _ _
    _ ≤ C * ‖z - z'‖ + ‖z - z'‖ := by gcongr; exact h z z' y
    _ = _ := by ring


-- created on 2026-09-26
