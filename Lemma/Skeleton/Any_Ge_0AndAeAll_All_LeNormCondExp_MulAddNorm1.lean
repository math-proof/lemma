import sympy.stats.markov_samples
import sympy.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Lemma.Skeleton.IntegrableG
import Lemma.Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Iterates.Any_Ge_0AndAll_LeNorm.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.IteratesOfResidual
import Lemma.Iterates.Measurable.of.AdaptedOnSamplePath
import Lemma.Iterates.AdaptedOnSamplePath.of.IteratesOfResidual
open MeasureTheory Iterates Real


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d}
  {μ : Measure (ℕ → S × S)} [IsFiniteMeasure μ] :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ k j, ‖μ[fun ω' => sk.G (sk.x k ω') (ω' j) | Filtration.piLE k] ω‖ ≤ C * (‖sk.x k ω‖ + 1) := by
-- proof
  obtain ⟨C, hC, h⟩ := Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (sk := sk))
  refine ⟨C, hC, ae_all_iff.2 fun k => ae_all_iff.2 fun j => ?_⟩
  have hm : Measurable[Filtration.piLE k] (fun ω => C * (‖sk.x k ω‖ + 1)) :=
    ((measurable_norm.comp (Measurable.of.AdaptedOnSamplePath (AdaptedOnSamplePath.of.IteratesOfResidual sk.hx) k)).add_const 1).const_mul C
  obtain ⟨C', -, hC'⟩ := Any_Ge_0AndAll_LeNorm.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.IteratesOfResidual sk.hx sk.hFlip k
  have hi : Integrable (fun ω => C * (‖sk.x k ω‖ + 1)) μ :=
    Integrable.of_bound (hm.mono (Filtration.piLE.le k) le_rfl).aestronglyMeasurable (C * (C' + 1)) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      exact hC' ω)
  filter_upwards [norm_condExp_le (μ := μ) (m := Filtration.piLE k) (fun ω' => sk.G (sk.x k ω') (ω' j)), condExp_mono (m := Filtration.piLE k) (Skeleton.IntegrableG k j).norm hi (ae_of_all _ fun ω => h (sk.x k ω) (ω j))] with ω h₁ h₂
  rw [condExp_of_stronglyMeasurable (Filtration.piLE.le k) hm.stronglyMeasurable hi] at h₂
  exact h₁.trans h₂


-- created on 2026-09-26