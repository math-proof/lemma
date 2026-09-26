import Lemma.Kernel.TrajProb.eq.Bind_Traj
import Lemma.Kernel.AeEqCondExp.of.AeAeEqCondExp.Le.Integrable_Bind.Integrable_Bind.StronglyMeasurable
import Lemma.Measure.Measurable_FrestrictLe_PiLE
import Lemma.Measure.Integrable_IteratesUpdate.of.Measurable.Any_All_LeNorm.Measurable.Le
import Lemma.Measure.AeEqCondExpIteratesUpdate.of.Integrable.Measurable.Measurable.Le
open MeasureTheory ProbabilityTheory Finset Kernel Preorder Filtration Measure


@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace Z]
  {n m : ℕ}
  {φ : Z × S → EuclideanVec d}
  {φ₁ : (Iic n → S) → Z}
-- given
  (h₀ : n ≤ m)
  (h₁ : Measurable φ)
  (h₂ : ∃ C, ∀ (ω : ℕ → S) s, ‖φ (φ₁ (frestrictLe n ω), s)‖ ≤ C)
  (h₃ : Measurable φ₁)
  (M : HomMarkovChainSpec S) :
-- imply
  (M.traj_prob : Measure (ℕ → S))[iterates_update h₀ φ φ₁ | piLE n] =ᵐ[(M.traj_prob : Measure (ℕ → S))]
    fun x => ∫ s, φ (φ₁ (frestrictLe n x), s) ∂(M.kernel ^ (m - n)) (x n) := by
-- proof
  have := M.markov_kernel
  have hG : StronglyMeasurable[piLE n] (fun x : ℕ → S => ∫ s, φ (φ₁ (frestrictLe n x), s) ∂(M.kernel ^ (m - n)) (x n)) :=
    ((h₁.comp ((h₃.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable.integral_kernel_prod_right' (κ := (M.kernel ^ (m - n)).comap_last n)).comp_measurable (Measurable_FrestrictLe_PiLE (X := fun _ => S) n)
  obtain ⟨C, hC⟩ := h₂
  rw [TrajProb.eq.Bind_Traj]
  apply AeEqCondExp.of.AeAeEqCondExp.Le.Integrable_Bind.Integrable_Bind.StronglyMeasurable hG
  · exact Integrable_IteratesUpdate.of.Measurable.Any_All_LeNorm.Measurable.Le h₀ h₁ ⟨C, hC⟩ h₃
  · apply Integrable.of_bound (hG.mono (piLE.le n)).aestronglyMeasurable C (ae_of_all _ fun x => ?_)
    apply (norm_integral_le_of_norm_le_const (ae_of_all _ fun s => hC x s)).trans
    simp
  · exact piLE.le n
  · exact ae_of_all _ fun x₀ => AeEqCondExpIteratesUpdate.of.Integrable.Measurable.Measurable.Le h₀ h₁ h₃ (Integrable_IteratesUpdate.of.Measurable.Any_All_LeNorm.Measurable.Le h₀ h₁ ⟨C, hC⟩ h₃)


-- created on 2026-09-26