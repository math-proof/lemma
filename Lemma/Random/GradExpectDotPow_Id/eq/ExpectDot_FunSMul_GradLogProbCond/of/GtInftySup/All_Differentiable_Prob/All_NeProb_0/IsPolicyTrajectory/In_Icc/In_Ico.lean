import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.In_Icc.In_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure Real
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 800000


/--
Generalized advantage estimation for a finite action/state alphabet
(Schulman et al., arXiv 1506.02438). Remigrated onto `Model` — applies the
CountableMeasure dens `In_Icc.In_Ico` specialization, discharging dens extras
(`Measurable`, `StronglyMeasurable`, score `Ms`, split `g`/`Cg` bounds) from
`[Fintype 𝒮] [Fintype 𝒜]` and `sup ‖∇π‖ < ∞`.

Keeps the pre-remigration lean binder count (γ, ℓ, conditional law, Differentiable, Grad
bound); remigration onto dens CM had briefly reintroduced dens `hmeas`/`hφ`/`hMs`/split bounds.

- [GAE dens CM](?module=Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.In_Icc.In_Ico)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  (hπ : Model.IsConditionalProbability M r s a)
  (h₂ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₃ : sup[θ, sₜ, aₜ] ‖∇[θ] M.π[θ] sₜ aₜ‖ < ∞)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1) :
-- imply
  letI : Model.IsPolicyTrajectory M r s a := hπ.htr
  letI : Model.AbsContJointAS M a s := hπ.haj
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
      (((γ * ℓ) ^ (id : ℕ → ℕ) ⬝ᵥ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  have hmeas : ∀ θ', Measurable (fun z : 𝒮 × 𝒜 => M.π[θ'] z.1 z.2) :=
    hStoch.measurable_π
  obtain ⟨C, hC⟩ := h₃
  have hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) :=
    fun sₜ aₜ => ⟨C, by
      rintro _ ⟨κ, rfl⟩
      exact hC ⟨(κ, (sₜ, aₜ)), rfl⟩⟩
  have h₃sum : sup[sₜ] (∑ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) < ∞ := by
    let Cg : ℝ := C * (Fintype.card 𝒜 : ℝ)
    refine ⟨Cg, ?_⟩
    rintro _ ⟨sₜ, rfl⟩
    have hle : ∀ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ≤ C := by
      intro u
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨κ, rfl⟩
      simpa [gradient, LinearIsometryEquiv.norm_map] using hC ⟨(κ, (sₜ, u)), rfl⟩
    calc
      ∑ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ≤ ∑ _u : 𝒜, C :=
        Finset.sum_le_sum fun u _ => hle u
      _ = Cg := by simp [Cg, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.π[θ] z.1 z.2)) :=
    StronglyMeasurable.of_discrete
  have hMsEx : ∃ Ms, ∀ y u, ‖∇[θ] Real.log (M.π[θ] y u)‖ ≤ Ms := by
    have hfin : BddAbove (Set.range fun z : 𝒮 × 𝒜 =>
        ‖∇[θ] Real.log (M.π[θ] z.1 z.2)‖) :=
      Set.Finite.bddAbove (Set.finite_range _)
    obtain ⟨Ms, hUB⟩ := hfin
    exact ⟨Ms, fun y u => hUB ⟨(y, u), rfl⟩⟩
  obtain ⟨Ms, hMs⟩ := hMsEx
  have hMssup : sup[y, u] ‖∇[θ] Real.log (M.π[θ] y u)‖ < ∞ :=
    ⟨Ms, by rintro _ ⟨p, rfl⟩; exact hMs p.1 p.2⟩
  exact GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.In_Icc.In_Ico
    (M := M) h₀ h₁ hπ hmeas h₂ h₃sum hBdd hφ hMssup hR


-- created on 2026-10-21
-- updated on 2026-11-18