import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Conditional expectation given a finite-valued random variable `X` is, on every atom `X = x`,
the expectation under the conditional measure `π[|X ⁻¹' {x}]`
(on atoms of probability `0` the conditional measure is `0`).
-/
@[main]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  {π : Measure Ω} [IsFiniteMeasure π]
  {X : Ω → S}
  {f : Ω → ℝ}
-- given
  (h₀ : Measurable X)
  (h₁ : Integrable f π) :
-- imply
  π[f | MeasurableSpace.comap X inferInstance] =ᵐ[π] fun ω ↦ ∫ ω', f ω' ∂π[|X ⁻¹' {X ω}] := by
-- proof
  classical
  have hm : MeasurableSpace.comap X inferInstance ≤ (inferInstance : MeasurableSpace Ω) := h₀.comap_le
  have hA : ∀ x, MeasurableSet (X ⁻¹' {x}) := fun x ↦ h₀ (measurableSet_singleton x)
  have hc : StronglyMeasurable (fun x : S ↦ ∫ ω', f ω' ∂π[|X ⁻¹' {x}]) := StronglyMeasurable.of_discrete
  have hgi : Integrable (fun ω ↦ ∫ ω', f ω' ∂π[|X ⁻¹' {X ω}]) π :=
    Integrable.of_bound (hc.comp_measurable h₀).aestronglyMeasurable (∑ x, ‖∫ ω', f ω' ∂π[|X ⁻¹' {x}]‖)
      (Filter.Eventually.of_forall fun ω ↦
        Finset.single_le_sum (f := fun x ↦ ‖∫ ω', f ω' ∂π[|X ⁻¹' {x}]‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ (X ω)))
  have hatom : ∀ x, ∫ ω in X ⁻¹' {x}, (∫ ω', f ω' ∂π[|X ⁻¹' {X ω}]) ∂π = ∫ ω in X ⁻¹' {x}, f ω ∂π := by
    intro x
    rw [setIntegral_congr_fun (hA x) (g := fun _ ↦ ∫ ω', f ω' ∂π[|X ⁻¹' {x}]) (fun ω hω ↦ by
      rw [show X ω = x from hω])]
    rw [setIntegral_const, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, smul_eq_mul]
    if h : π (X ⁻¹' {x}) = 0 then
      rw [Measure.restrict_eq_zero.2 h]
      simp
    else
      rw [ENNReal.toReal_inv, ← measureReal_def, ← mul_assoc,
        mul_inv_cancel₀ ((measureReal_eq_zero_iff (measure_ne_top _ _)).not.2 h), one_mul]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm h₁ (fun _ _ _ ↦ hgi.integrableOn) ?_
    ((hc.comp_measurable (comap_measurable X)).aestronglyMeasurable)).symm
  rintro _ ⟨T, -, rfl⟩ -
  have hT : X ⁻¹' T = ⋃ x ∈ Finset.univ.filter (· ∈ T), X ⁻¹' {x} := by
    ext ω
    simp
  have hdisj : Set.Pairwise (↑(Finset.univ.filter (· ∈ T))) (Function.onFun Disjoint fun x ↦ X ⁻¹' {x}) :=
    fun x _ y _ hxy ↦ Set.disjoint_left.2 fun ω h₁ h₂ ↦ hxy ((show X ω = x from h₁).symm.trans h₂)
  rw [hT, integral_biUnion_finset _ (fun x _ ↦ hA x) hdisj (fun _ _ ↦ hgi.integrableOn),
    integral_biUnion_finset _ (fun x _ ↦ hA x) hdisj (fun _ _ ↦ h₁.integrableOn)]
  exact Finset.sum_congr rfl fun x _ ↦ hatom x


-- created on 2026-10-06
