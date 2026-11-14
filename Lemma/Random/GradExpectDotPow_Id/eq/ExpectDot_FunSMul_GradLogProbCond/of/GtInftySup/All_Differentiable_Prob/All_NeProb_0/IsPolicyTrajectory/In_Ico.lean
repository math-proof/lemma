import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Syntax.Order.Sup
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real
set_option maxHeartbeats 900000


/--
Unbiased advantage estimate for a finite action/state alphabet (`[Fintype 𝒮] [Fintype 𝒜]`):
with `V_θ[t] δ k := M.V θ γ (t + k) (δ k)` and score `∇ log π`,
`∇𝔼[(γ ^ id) ⬝ᵥ r] = 𝔼[(γ ^ id) ⬝ᵥ fun t ↦ ((γ ^ id) ⬝ᵥ (r[t:] + γ • V_θ[t+1] s[t+1:] - V_θ[t] s[t:])) • ∇ log π]`.

Remigrated onto `DensityModel` — applies dens FunSMul `In_Ico`, discharging dens extras
(`Measurable`, Integrable/integral bounds, `StronglyMeasurable`, score `Ms`, split `g`/`Cg`)
from `[Fintype 𝒮] [Fintype 𝒜]` / counting measure and `sup ‖∇π‖ < ∞`.

Keeps the pre-remigration lean binder count (γ, conditional law, Differentiable, Grad bound).

- [GAE dens FunSMul](?module=Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hπ : DensityModel.IsConditionalProbability M r s a)
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun t δ k => M.V θ γ (t + k) (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
-- proof
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := hπ.htr.stage_eq
  have hmeas : ∀ θ', Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ' z.1 z.2) :=
    M.policy.measurable_prob
  obtain ⟨C, hC⟩ := h₃
  let g : 𝒮 → 𝒜 → ℝ := fun _ _ => C
  have h₃bound : ∀ θ' x u, ‖fderiv ℝ (fun θ'' => M.policy.prob θ'' x u) θ'‖ ≤ g x u := by
    intro θ' x u
    have hnorm :
        ‖fderiv ℝ (fun θ'' => M.policy.prob θ'' x u) θ'‖ =
          ‖∇[θ'] M.policy.prob θ' x u‖ := by
      simp [gradient]
    rw [hnorm]
    exact hC ⟨(θ', (x, u)), rfl⟩
  let Cg : ℝ := C * (Fintype.card 𝒜 : ℝ)
  have h₄ : ∀ x, ∑ u, g x u ≤ Cg := by
    intro x
    simp [g, Cg, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hμ : (ReferenceMeasure.measure : Measure 𝒜) = Measure.count :=
    CountableMeasure.measure_eq_count
  have h₄' : ∀ x, Integrable (g x) ReferenceMeasure.measure := by
    intro x
    rw [hμ]
    exact (integrable_count_iff).mpr Summable.of_finite
  have h₅' : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg := by
    intro x
    rw [hμ, integral_count]
    exact h₄ x
  have hφ : StronglyMeasurable
      (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ) :=
    StronglyMeasurable.of_discrete
  have hMsEx : ∃ Ms, ∀ y u,
      ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms := by
    have hfin : BddAbove (Set.range fun z : 𝒮 × 𝒜 =>
        ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ‖) :=
      Set.Finite.bddAbove (Set.finite_range _)
    obtain ⟨Ms, hUB⟩ := hfin
    exact ⟨Ms, fun y u => hUB ⟨(y, u), rfl⟩⟩
  obtain ⟨Ms, hMs⟩ := hMsEx
  have h₅sup : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞ :=
    ⟨Cg, by rintro _ ⟨x, rfl⟩; exact h₅' x⟩
  have hMssup : sup[y, u] ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ < ∞ :=
    ⟨Ms, by rintro _ ⟨p, rfl⟩; exact hMs p.1 p.2⟩
  have hVm : ∀ k, Measurable (M.V θ γ k) := fun _ => Measurable.of_discrete
  exact GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
    (M := M) (g := g) h₀ h₁ hmeas hVm h₂ h₃bound h₄' h₅sup hφ hMssup


-- created on 2026-10-21
-- updated on 2026-11-14
