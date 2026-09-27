import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Lemma.Filter.Sum.of.All_Eq
open Filter MeasureTheory
open scoped RealInnerProductSpace


@[main]
private lemma main
  {m m₀ : MeasurableSpace Ω}
  {μ : Measure[m₀] Ω}
  {f g : Ω → EuclideanSpace ℝ (Fin d)}
-- given
  (h₀ : Integrable g μ)
  (h₁ : ∀ i, Integrable ((fun ω ↦ f ω i) * fun ω ↦ g ω i) μ)
  (h₂ : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ f ω i) μ) :
-- imply
  μ[fun ω => ⟪f ω, g ω⟫ | m] =ᵐ[μ] fun ω => ⟪f ω, μ[g | m] ω⟫ := by
-- proof
  have hg : ∀ i, Integrable (fun ω => g ω i) μ := fun i => (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integrable_comp h₀
  calc
    _ = μ[∑ i, (fun ω => f ω i) * (fun ω => g ω i) | m] := by
      congr 1
      ext ω
      simp [PiLp.inner_apply, Finset.sum_apply, mul_comm]
    _ =ᵐ[μ] ∑ i, μ[(fun ω => f ω i) * (fun ω => g ω i) | m] := condExp_finsetSum (fun i _ => h₁ i) m
    _ =ᵐ[μ] ∑ i, (fun ω => f ω i) * μ[fun ω => g ω i | m] :=
      Sum.of.All_Eq fun i _ => condExp_mul_of_aestronglyMeasurable_left (h₂ i) (h₁ i) (hg i)
    _ =ᵐ[μ] _ := by
      filter_upwards [ae_all_iff.2 fun i => (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp_condExp_comm (m := m) h₀] with ω hω
      simp only [Finset.sum_apply, Pi.mul_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hω i
      simp [Function.comp_def] at this
      rw [← this, mul_comm]


-- created on 2026-09-26