import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.EqProb
import Mathlib.Analysis.Calculus.Gradient.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real Measure
open scoped ENNReal.ToRealCoe
open IsPolicyTrajectory


/--
Ae equality: binder-equality ℙ-log-grad vs `M.policy.prob` log-grad.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : IsPolicyTrajectory M r s a)
  (h₁ : ∀ θ («s.bvar» : ℕ ⇀ S), ℙ[M θ](s[0] = «s.bvar»[0]) ≠ 0)
  (h₂ : ∀ t («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)))
  (h₃ : sup[θ, t, «s.bvar» : ℕ ⇀ S, «a.bvar» : ℕ ⇀ A]
    ‖∇[θ] (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    IsPolicyTrajectory.singlePSpace_as (h := h₀) _ t
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    IsPolicyTrajectory.singlePSpace_s (h := h₀) _ t
  ∀ t, ∀ᵐ ω ∂(M θ),
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log =
        ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) := by
-- proof
  intro hP _ 
  have : IsPolicyTrajectory M r s a := h₀
  classical
  have hP0raw : ∀ θ' x, (M θ').real ((s 0) ⁻¹' {x}) ≠ 0 := by
    intro θ' x
    have heqR : (ℙ[M θ'](s[0] = x) : ℝ) = (M θ').real ((s 0) ⁻¹' {x}) := by
      rw [EqProb («π» := M θ') (x := s 0) x]
      rfl
    have heqE : ℙ[M θ'](s[0] = x) = (M θ') ((s 0) ⁻¹' {x}) :=
      EqProb («π» := M θ') (x := s 0) x
    rw [← heqR]
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨h₁ θ' ⟨fun _ => x⟩, heqE ▸ measure_ne_top (M θ') _⟩
  have h_pol_eq : ∀ θ' x u, (ℙ[M θ']((a 0) = u | (s 0) = x) : ℝ) = M.policy.prob θ' x u := by
    intro θ' x u
    erw [ProbCond.eq.OfRealPol.of.Ne_0 h₀.stage_eq (hP θ' 0) (hP0raw θ' x),
      ENNReal.toReal_ofReal (M.policy.nonneg θ' x u)]
  have hDiffPol : ∀ x u, Differentiable ℝ (M.policy.prob · x u) := by
    intro x u
    exact (funext fun θ' => (h_pol_eq θ' x u).symm) ▸ h₂ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩
  have hSupPol : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞ := by
    obtain ⟨C, hC⟩ := h₃
    refine ⟨C, ?_⟩
    rintro _ ⟨⟨θ', x, u⟩, rfl⟩
    have hgrad : ∇[θ'] M.policy.prob θ' x u =
        ∇[θ'] (ℙ[M θ']((a 0) = u | (s 0) = x) : ℝ) := by
      refine Filter.EventuallyEq.gradient_eq ?_
      exact Filter.Eventually.of_forall fun θ'' => (h_pol_eq θ'' x u).symm
    change ‖∇[θ'] M.policy.prob θ' x u‖ ≤ C
    rw [hgrad]
    apply hC
    exact ⟨(θ', (0 : ℕ), (⟨fun _ => x⟩ : ℕ ⇀ S), (⟨fun _ => u⟩ : ℕ ⇀ A)), rfl⟩
  intro t
  filter_upwards [AeRealPreimageSS.ne.Zero (s := ⇑s) (M := M) θ] with ω hω
  have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
    (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M)
      h₀.stage_eq hDiffPol hSupPol t (s t ω) θ).continuousAt
  have hfd :
    fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₀.stage_eq (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  simp only [gradient]
  apply congrArg (InnerProductSpace.toDual ℝ Θ).symm hfd


-- created on 2026-10-21
-- updated on 2026-10-23
