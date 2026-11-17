import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Syntax.Order.Sup
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Instance.Analysis.Real.Numbers
import Class.Dynamics.PolicyTrajectory
open scoped ENNReal.ToRealCoe
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure Real
set_option maxHeartbeats 900000


/--
Unbiased advantage estimate for a finite action/state alphabet (`[Fintype 𝒮] [Fintype 𝒜]`):
with `V_θ[t] δ k := M.V θ γ (t + k) (δ k)` and score `∇ log π`,
`∇𝔼[(γ ^ id) ⬝ᵥ r] = 𝔼[(γ ^ id) ⬝ᵥ fun t ↦ ((γ ^ id) ⬝ᵥ (r[t:] + γ • V_θ[t+1] s[t+1:] - V_θ[t] s[t:])) • ∇ log π]`.

Remigrated onto `Model` — applies dens FunSMul `In_Ico`, discharging dens extras
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
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hπ : Model.IsConditionalProbability M r s a)
  (h₂ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₃ : sup[θ, sₜ, aₜ] ‖∇[θ] M.π[θ] sₜ aₜ‖ < ∞) :
-- imply
  have : ∀ θ', PSpace (M.traj θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M.traj θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M.traj θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun t δ k => M.V θ γ (t + k) (δ k)⟩
  ∇[θ] 𝔼[r: M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] Real.log (M.π[θ] (s t) (a t)))) := by
-- proof
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := hπ.htr.stage_eq
  have hmeas : ∀ θ', Measurable (fun z : 𝒮 × 𝒜 => M.π[θ'] z.1 z.2) :=
    hStoch.measurable_π
  obtain ⟨C, hC⟩ := h₃
  have hμ : (ReferenceMeasure.measure : Measure 𝒜) = Measure.count :=
    CountableMeasure.measure_eq_count
  have hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) :=
    fun sₜ aₜ => ⟨C, by
      rintro _ ⟨κ, rfl⟩
      exact hC ⟨(κ, (sₜ, aₜ)), rfl⟩⟩
  have hIntg : ∀ sₜ, Integrable
      (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
      ReferenceMeasure.measure := fun sₜ => by
    rw [hμ]
    exact integrable_count_iff.mpr Summable.of_finite
  have h₅sup : sup[sₜ] (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂ReferenceMeasure.measure) < ∞ := by
    let Cg : ℝ := C * (Fintype.card 𝒜 : ℝ)
    refine ⟨Cg, ?_⟩
    rintro _ ⟨sₜ, rfl⟩
    have hle : ∀ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ≤ C := by
      intro u
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨κ, rfl⟩
      simpa [gradient, LinearIsometryEquiv.norm_map] using hC ⟨(κ, (sₜ, u)), rfl⟩
    change (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂ReferenceMeasure.measure) ≤ Cg
    rw [hμ, integral_count]
    calc
      ∑ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ≤ ∑ _u : 𝒜, C := Finset.sum_le_sum fun u _ => hle u
      _ = Cg := by simp [Cg, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hφ : StronglyMeasurable
      (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.π[θ'] z.1 z.2)) θ) :=
    StronglyMeasurable.of_discrete
  have hMsEx : ∃ Ms, ∀ y u,
      ‖fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖ ≤ Ms := by
    have hfin : BddAbove (Set.range fun z : 𝒮 × 𝒜 =>
        ‖fderiv ℝ (fun θ' => Real.log (M.π[θ'] z.1 z.2)) θ‖) :=
      Set.Finite.bddAbove (Set.finite_range _)
    obtain ⟨Ms, hUB⟩ := hfin
    exact ⟨Ms, fun y u => hUB ⟨(y, u), rfl⟩⟩
  obtain ⟨Ms, hMs⟩ := hMsEx
  have hMssup : sup[y, u] ‖fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖ < ∞ :=
    ⟨Ms, by rintro _ ⟨p, rfl⟩; exact hMs p.1 p.2⟩
  have hVm : ∀ k, Measurable (M.V θ γ k) := fun _ => Measurable.of_discrete
  exact GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
    (M := M) h₀ h₁ hmeas hVm h₂ h₅sup hBdd hIntg hφ hMssup


-- created on 2026-10-21
-- updated on 2026-11-16
