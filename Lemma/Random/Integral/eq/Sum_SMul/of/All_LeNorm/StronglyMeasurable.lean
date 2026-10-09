import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Integral against the stage kernel of the trajectory model `M`, for a bounded strongly measurable `f`:
`∫ z, f z ∂(stageK θ y) = ∑ u, π_θ(u | y) • ∫ ρ, f (ρ, y, u) ∂(reward (y, u))`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Model Θ S A}
  {f : ℝ × S × A → E}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (y : S) :
-- imply
  ∫ z, f z ∂(M.stageK θ y) = ∑ u, M.pol.prob θ y u • ∫ ρ, f (ρ, y, u) ∂(M.env.reward (y, u)) := by
-- proof
  have := M.env.reward_markov
  unfold Model.stageK
  rw [Kernel.map_apply _ (by fun_prop), integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [Kernel.prod_apply, Kernel.deterministic_apply]
  rw [id, Measure.dirac_prod, integral_map (f := fun x : S × A × ℝ => f (x.2.2, x.1, x.2.1)) (by fun_prop)
    (hf.comp_measurable (by fun_prop)).aestronglyMeasurable]
  rw [ProbabilityTheory.integral_compProd (f := fun x : A × ℝ => f (x.2, y, x.1))
    (Integrable.of_bound (hf.comp_measurable (by fun_prop)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC _))]
  have hb : ∀ u, ‖∫ ρ, f (ρ, y, u) ∂(M.env.reward (y, u))‖ ≤ C := by
    intro u
    calc _ ≤ ∫ ρ, ‖f (ρ, y, u)‖ ∂(M.env.reward (y, u)) := norm_integral_le_integral_norm _
      _ ≤ ∫ ρ, C ∂(M.env.reward (y, u)) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const C) (Filter.Eventually.of_forall fun ρ => hC _)
      _ = C := by simp
  rw [integral_fintype (Integrable.of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable C
    (Filter.Eventually.of_forall hb))]
  congr 1
  funext u
  congr 1
  show ((M.pol.measure θ y) {u}).toReal = _
  rw [Policy.measure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton u), smul_eq_mul]
  rw [Finset.sum_eq_single u (fun b _ hb => by simp [hb]) (by simp)]
  simp [M.pol.nonneg θ y u]


-- created on 2026-10-07
