import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.In_Icc.In_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 800000


/--
Generalized advantage estimation for a finite action/state alphabet
(Schulman et al., arXiv 1506.02438). Remigrated onto `DensityModel` — applies the
CountableMeasure dens `In_Icc.In_Ico` specialization, discharging dens extras
(`Measurable`, `StronglyMeasurable`, score `Ms`, split `g`/`Cg` bounds) from
`[Fintype S] [Fintype A]` and `sup ‖∇π‖ < ∞`.

Keeps the pre-remigration lean binder count (γ, ℓ, conditional law, Differentiable, Grad
bound); remigration onto dens CM had briefly reintroduced dens `hmeas`/`hφ`/`hMs`/split bounds.

- [GAE dens CM](?module=Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.In_Icc.In_Ico)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  (hπ : DensityModel.IsConditionalProbability M r s a)
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞) :
-- imply
  letI : DensityModel.IsPolicyTrajectory M r s a := hπ.htr
  letI : DensityModel.AbsContJointAS M a s := hπ.haj
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun _ δ k => M.V0 θ γ (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  have hmeas : ∀ θ', Measurable (fun z : S × A => M.policy.prob θ' z.1 z.2) :=
    M.policy.measurable_prob
  obtain ⟨C, hC⟩ := h₃
  let g : S → A → ℝ := fun _ _ => C
  have h₃bound : ∀ θ' x u, ‖∇[θ'] M.policy.prob θ' x u‖ ≤ g x u := by
    intro θ' x u
    exact hC ⟨(θ', (x, u)), rfl⟩
  let Cg : ℝ := C * (Fintype.card A : ℝ)
  have h₄ : ∀ x, ∑ u, g x u ≤ Cg := by
    intro x
    simp [g, Cg, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hφ : StronglyMeasurable
      (fun z : S × A => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)) :=
    StronglyMeasurable.of_discrete
  have hMsEx : ∃ Ms, ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ Ms := by
    have hfin : BddAbove (Set.range fun z : S × A =>
        ‖∇[θ] Real.log (M.policy.prob θ z.1 z.2)‖) :=
      Set.Finite.bddAbove (Set.finite_range _)
    obtain ⟨Ms, hUB⟩ := hfin
    exact ⟨Ms, fun y u => hUB ⟨(y, u), rfl⟩⟩
  obtain ⟨Ms, hMs⟩ := hMsEx
  exact GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.In_Icc.In_Ico
    (M := M) (Cg := Cg) (Ms := Ms) (g := g) h₀ h₁ hπ hmeas h₂ h₃bound h₄ hφ hMs


-- created on 2026-10-21
-- updated on 2026-11-04
