import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
import Lemma.Real.MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico
import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity.All_Eq_JointDens
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open Finset (range)
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real
open IsPolicyTrajectory
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false


/--
Generalized advantage estimation with the paper's weighted-average estimator (Schulman et al.,
arXiv 1506.02438, Eq. (16)) for continuous actions: with TD residuals
`δ[j] = r[j] + γ * Vkd(s[j+1]) - Vkd(s[j])` and `{γ, ℓ} ⊆ Ico 0 1`, the exponentially weighted
average `(1 - ℓ) * ((ℓ ^ id) @ fun k ↦ (γ ^ range(k+1)) @ δ)` equals the closed form, via
`Real.MulSub1_Dot_FunDotPow_Range.…Subset_Ico` and
`AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity`, applying the continuous closed-form GAE.

Given hyps and the imply score use `IsPolicyTrajectory` and the `ℙ` conditional-density sugar
(mirroring the discrete `IsPolicyTrajectory` Subset_Ico): Fun binders `ℕ ⇀ S` / `ℕ ⇀ A`
appear as `s[t] = «s.bvar»[t]` / `a[t] = «a.bvar»[t]` (not point values `x` / `u`). The score is
`∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log` under `𝔼[r, s, a : M θ]` (so `desugarProbRA` applies).
Absolute continuity of `law(s[t])` and `law(a[t], s[t])` (`AbsContStateMarginal` /
`AbsContJointAS`) is required for `SinglePSpace` / `ℙ` elaboration and is not implied by `Env`
alone. Pointwise joint-density factorization `hfactor` (policy dens × state RN derivative) and
`hdens` (state dens ≠ 0, ≠ ⊤ everywhere) discharge the Fun-binder bridge
`ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity.All_Eq_JointDens` inside the proof
(mirroring discrete `All_NeProb_0` + `OfRealPol.of.Ne_0`); Radon–Nikodym versions are unique
only a.e., so `hfactor` remains an explicit continuous-version choice until a `stageK`
pointwise lift is available. The proof specializes to constant paths for the `policy.prob`
form expected by `In_Icc.In_Ico`. The old redundant `hπ : Measurable (policy.prob …)` is
dropped (`DensityPolicy.measurable_prob`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : {γ, ℓ} ⊆ Set.Ico 0 1)
  (h₁ : DensityModel.IsPolicyTrajectory M r s a)
  (hacc : DensityModel.AbsContStateMarginal M s)
  (haj : DensityModel.AbsContJointAS M a s)
  (hfactor : ∀ θ t x u,
    (M θ).prob (a t, s t) (u, x) =
      ENNReal.ofReal (M.policy.prob θ x u) *
        ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x)
  (hdens : ∀ θ t x,
    ℙ[M θ](s[t] = x) ≠ 0 ∧ ℙ[M θ](s[t] = x) ≠ ⊤)
  (h₂ : ∀ t («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)))
  (h₃ : ∃ (g : S → A → ℝ),
    (∀ θ t («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
      ‖∇[θ] (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)‖ ≤
        g «s.bvar»[t] «a.bvar»[t]) ∧
    (∀ x, Integrable (g x) ReferenceMeasure.measure) ∧
    (sup[x] (∫ u, g x u ∂ReferenceMeasure.measure) < ∞))
  (hφ : StronglyMeasurable
    (fun ((x, u) : S × A) => ∇[θ] (ℙ[M θ](a[0] = u | s[0] = x) : ℝ).log))
  (hMs : sup[«s.bvar» : ℕ ⇀ S, «a.bvar» : ℕ ⇀ A]
    ‖∇[θ] (ℙ[M θ](a[0] = «a.bvar»[0] | s[0] = «s.bvar»[0]) : ℝ).log‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun θ t =>
    h₁.singlePSpace_as (haj := haj) θ t
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun θ t =>
    h₁.singlePSpace_s (hac := hacc) θ t
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(h₁.measurable_r t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(h₁.measurable_s t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(h₁.measurable_a t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun _ δ k => M.Vkd θ γ (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      (((1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ (γ ^ range (k + 1)) @
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:]))) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  intro hPas hPs _ _ _ _ V_θ
  haveI : DensityModel.IsPolicyTrajectory M r s a := h₁
  haveI : DensityModel.AbsContStateMarginal M s := hacc
  haveI : DensityModel.AbsContJointAS M a s := haj
  have hπeq : ∀ θ t («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
      (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ) =
        M.policy.prob θ «s.bvar»[t] «a.bvar»[t] := fun θ t sb ab =>
    ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity.All_Eq_JointDens
      (M := M) h₁ haj (hfactor θ t (sb t) (ab t))
      (hdens θ t (sb t)).1 (hdens θ t (sb t)).2
  simp only [FinsetPow.dot_eq]
  classical
  have hγ : γ ∈ Set.Ico 0 1 := h₀ (by simp)
  have hℓ₀ : ℓ ∈ Set.Ico 0 1 := h₀ (by simp)
  have hℓ : ℓ ∈ Set.Icc 0 1 := ⟨hℓ₀.1, hℓ₀.2.le⟩
  have hπ : ∀ θ', Measurable (fun z : S × A => M.policy.prob θ' z.1 z.2) :=
    M.policy.measurable_prob
  obtain ⟨g, ⟨h₃bound, ⟨h₄, h₅sup⟩⟩⟩ := h₃
  obtain ⟨Cg, h₅UB⟩ := h₅sup
  have h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg := fun x =>
    h₅UB (Set.mem_range_self x)
  -- specialize Fun binders to constant paths for In_Icc's pointwise policy.prob hyps
  have h₂pol : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u) := fun x u =>
    (funext fun θ' => (hπeq θ' 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩).symm) ▸
      h₂ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩
  have h₃pol : ∀ θ' x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ'‖ ≤ g x u := by
    intro θ' x u
    have hfe : (fun θ => M.policy.prob θ x u) =
        (fun θ => (ℙ[M θ](a[0] = (⟨fun _ => u⟩ : ℕ ⇀ A)[0] |
          s[0] = (⟨fun _ => x⟩ : ℕ ⇀ S)[0]) : ℝ)) :=
      funext fun θ'' => (hπeq θ'' 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩).symm
    have := h₃bound θ' 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩
    simpa [hfe, gradient, LinearIsometryEquiv.norm_map] using this
  have hφpol : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ) := by
    have hφ' : StronglyMeasurable
      (fun z : S × A => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)) := by
      convert hφ using 1
      funext z
      refine congrArg (gradient · θ) ?_
      funext θ'
      simp only [hπeq θ' 0 ⟨fun _ => z.1⟩ ⟨fun _ => z.2⟩]
    simpa [gradient] using
      (InnerProductSpace.toDual ℝ Θ).continuous.comp_stronglyMeasurable hφ'
  obtain ⟨Ms, hMsUB⟩ := hMs
  have hMspol : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms := by
    intro y u
    have hfe : (fun θ' => Real.log (M.policy.prob θ' y u)) =
        (fun θ' => (ℙ[M θ'](a[0] = (⟨fun _ => u⟩ : ℕ ⇀ A)[0] |
          s[0] = (⟨fun _ => y⟩ : ℕ ⇀ S)[0]) : ℝ).log) :=
      funext fun θ' => congrArg Real.log (hπeq θ' 0 ⟨fun _ => y⟩ ⟨fun _ => u⟩).symm
    have := hMsUB (Set.mem_range_self (⟨fun _ => y⟩, ⟨fun _ => u⟩))
    simpa [hfe, gradient, LinearIsometryEquiv.norm_map] using this
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁.stage_eq t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁.stage_eq t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁.stage_eq t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have h₁' : ∀ t, (· t) = (r t, s t, a t) := fun t => by
    funext ω; rfl
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst h₁' t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁' t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁' t).aemeasurable⟩)
  haveI : ∀ θ' t, SinglePSpace (M θ') (a t, s t) := fun θ' t =>
    h₁.singlePSpace_as (haj := haj) θ' t
  haveI : ∀ θ' t, SinglePSpace (M θ') (s t) := fun θ' t =>
    h₁.singlePSpace_s (hac := hacc) θ' t
  have hscore : ∀ t (x : S) (u : A),
      gradient (fun θ' : Θ => Real.log (M.policy.prob θ' x u)) θ =
        gradient (fun θ' : Θ => (ℙ[M θ']((a t) = u | (s t) = x) : ℝ).log) θ := by
    intro t x u
    have hfe : (fun θ' : Θ => Real.log (M.policy.prob θ' x u)) =
        (fun θ' : Θ => (ℙ[M θ']((a t) = u | (s t) = x) : ℝ).log) :=
      funext fun θ' =>
        congrArg Real.log (hπeq θ' t ⟨fun _ => x⟩ ⟨fun _ => u⟩).symm
    simp only [hfe]
  have hφg : StronglyMeasurable
    (fun z : S × A => gradient (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ) := by
    simp only [gradient]
    exact ((InnerProductSpace.toDual ℝ Θ).symm.continuous.comp_stronglyMeasurable hφpol)
  have hφgℙ : ∀ t, StronglyMeasurable fun z : S × A =>
      gradient (fun θ' : Θ => (ℙ[M θ']((a t) = z.2 | (s t) = z.1) : ℝ).log) θ := fun t => by
    convert hφg using 1
    funext z
    exact (hscore t z.1 z.2).symm
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
    r k ω + γ * M.Vkd θ γ (s (k + 1) ω) - M.Vkd θ γ (s k ω) := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₁' k).add
      (((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
          (Random.Measurable.of.All_Eq.snd.fst h₁' (k + 1))).const_mul γ)).sub
      ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁' k))
  have hbdd : ∀ᵐ ω ∂(M θ),
      BddAbove (Set.range fun j =>
        |r j ω + γ * M.Vkd θ γ (s (j + 1) ω) - M.Vkd θ γ (s j ω)|) := by
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) hγ h₁' θ] with ω h1
    refine ⟨(3 / (1 - γ) - 1) * |M.env.R|, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := h1 j
    rwa [Real.norm_eq_abs] at this
  have hpt : ∀ᵐ ω ∂(M θ), ∀ t,
    (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) ω + γ * M.Vkd θ γ (s (t + i + 1) ω) - M.Vkd θ γ (s (t + i) ω))) =
    ((γ * ℓ) ^ (id : ℕ → ℕ)) @
      (fun k : ℕ => r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) - M.Vkd θ γ (s (t + k) ω)) := by
    filter_upwards [hbdd] with ω hb t
    exact MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico
      (δ := ⟨fun j => r j ω + γ * M.Vkd θ γ (s (j + 1) ω) - M.Vkd θ γ (s j ω)⟩) (t := t) h₀ hb
  have hexp_pol : ∀ F : ℕ → (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℝ,
    (∀ t, Measurable fun ω : ℕ → ℝ × S × A => F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω)) →
    𝔼[r, s, a : M θ](
      (γ ^ (id : ℕ → ℕ)) @ fun t ↦ (F t s a r •
        ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) =
    ∫ ω, ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
      ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) := by
    intro F hF
    have hg := fun t : ℕ =>
      StronglyMeasurable.smul (hF t).stronglyMeasurable
        (hφg.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁' t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁' t)))
    have hGsm : StronglyMeasurable fun ω : ℕ → ℝ × S × A =>
      ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
        ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) :=
      StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        (hg t).const_smul (γ ^ t)
    let fromPath := fun (p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A)) =>
      fun t => (p.1 t, p.2.1 t, p.2.2 t)
    have fromPath_meas : Measurable fromPath :=
      Measurable.of_eval fun t =>
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))
    have hx : AEMeasurable
      (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
      PSpace.aemeasurable
    simp only [AsPathRV.path_process]
    rw [Expectation.ofRV, expectation_bochner]
    refine (integral_map hx ?_).trans ?_
    ·
      exact (hGsm.comp_measurable fromPath_meas).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun p => by
          simp only [Function.comp_apply, fromPath]
          rfl)
    simp only [AsPathRV.path_process, JointRandomSymbol]
    rfl
  have hexp : ∀ F : ℕ → (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℝ,
    (∀ t, Measurable fun ω : ℕ → ℝ × S × A => F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω)) →
    𝔼[r, s, a : M θ](
      (γ ^ (id : ℕ → ℕ)) @ fun t ↦ (F t s a r •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) =
    ∫ ω, ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) ∂(M θ) := by
    intro F hF
    have hg := fun t : ℕ =>
      StronglyMeasurable.smul (hF t).stronglyMeasurable
        ((hφgℙ t).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁' t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁' t)))
    have hGsm : StronglyMeasurable fun ω : ℕ → ℝ × S × A =>
      ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
        ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) :=
      StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        (hg t).const_smul (γ ^ t)
    let fromPath := fun (p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A)) =>
      fun t => (p.1 t, p.2.1 t, p.2.2 t)
    have fromPath_meas : Measurable fromPath :=
      Measurable.of_eval fun t =>
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))
    have hx : AEMeasurable
      (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
      PSpace.aemeasurable
    simp only [AsPathRV.path_process]
    rw [Expectation.ofRV, expectation_bochner]
    refine (integral_map hx ?_).trans ?_
    ·
      exact (hGsm.comp_measurable fromPath_meas).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun p => by
          simp only [Function.comp_apply, fromPath]
          rfl)
    simp only [AsPathRV.path_process, JointRandomSymbol]
    rfl
  have hF₁ : ∀ t, Measurable fun ω : ℕ → ℝ × S × A =>
    (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) ω + γ * M.Vkd θ γ (s (t + i + 1) ω) - M.Vkd θ γ (s (t + i) ω))) := fun t => by
    show Measurable fun ω : ℕ → ℝ × S × A =>
      (1 - ℓ) * ∑' k, ℓ ^ k * ∑ i ∈ range (k + 1), γ ^ i *
        (r (t + i) ω + γ * M.Vkd θ γ (s (t + i + 1) ω) - M.Vkd θ γ (s (t + i) ω))
    exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
      (Finset.measurable_sum _ fun i _ => (hmeas (t + i)).const_mul _).const_mul _).const_mul _
  have hF₂ : ∀ t, Measurable fun ω : ℕ → ℝ × S × A =>
    (((γ * ℓ) ^ (id : ℕ → ℕ)) @
      (fun k : ℕ => r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) - M.Vkd θ γ (s (t + k) ω))) := fun t => by
    show Measurable fun ω : ℕ → ℝ × S × A => ∑' k, (γ * ℓ) ^ k *
      (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) - M.Vkd θ γ (s (t + k) ω))
    exact Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k => (hmeas (t + k)).const_mul _
  have hδθ : ∀ (s : ℕ → S) (r : ℕ → ℝ) (t : ℕ),
    (fun k => r (t + k) + γ * M.Vkd θ γ (s (t + k + 1)) - M.Vkd θ γ (s (t + k))) =
      r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:] := by
    intro s r t
    funext k
    have hk : t + k + 1 = t + 1 + k := by omega
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_θ,
      Function.getSliceFrom_apply, hk]
  have hFθ : ∀ t, Measurable fun ω : ℕ → ℝ × S × A =>
    (((γ * ℓ) ^ (id : ℕ → ℕ)) @
      ((fun j => r j ω)[t:] + γ • V_θ[t + 1] (fun j => s j ω)[t + 1:] -
        V_θ[t] (fun j => s j ω)[t:])) := fun t => by
    convert hF₂ t using 1
    funext ω
    exact congrArg (fun δ => Dot.dot ((γ * ℓ) ^ (id : ℕ → ℕ)) δ)
      (hδθ (fun j => s j ω) (fun j => r j ω) t).symm
  refine (GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
    (M := M) (θ := θ) (r := ⟨r⟩) (s := ⟨s⟩) (a := ⟨a⟩) hγ hℓ h₁' hπ h₂pol h₃pol h₄ h₅ hφpol hMspol).trans ?_
  -- In_Icc concludes with `policy.prob`; rewrite that score to the imply `ℙ` RA form via `hπeq`
  have hπRHS :
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((((γ * ℓ) ^ (id : ℕ → ℕ)) @
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((((γ * ℓ) ^ (id : ℕ → ℕ)) @
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) :=
    (hexp_pol (fun t s a r => ((γ * ℓ) ^ (id : ℕ → ℕ)) @
      (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) hFθ).trans <|
      (integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        tsum_congr fun t => by rw [hscore t (s t ω) (a t ω)])).trans
        (hexp (fun t s a r => ((γ * ℓ) ^ (id : ℕ → ℕ)) @
          (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) hFθ).symm
  refine hπRHS.trans ?_
  symm
  have hFeq :
    (fun t (s : ℕ → S) (a : ℕ → A) (r : ℕ → ℝ) =>
        (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
          (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:]) i)) =
      (fun t s a r =>
        (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
          (r (t + i) + γ * M.Vkd θ γ (s (t + i + 1)) - M.Vkd θ γ (s (t + i))))) := by
    funext t s a r
    congr 1
    congr 1
    funext k
    refine Finset.sum_congr rfl fun i _ => ?_
    have hk : t + i + 1 = t + 1 + i := by omega
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_θ,
      Function.getSliceFrom_apply, hk]
  refine (congrArg
      (fun F : ℕ → (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℝ =>
        𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
          (F t (fun j => s j) (fun j => a j) (fun j => r j) •
            ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)))
      hFeq).trans ?_
  refine (hexp (fun t s a r => (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) + γ * M.Vkd θ γ (s (t + i + 1)) - M.Vkd θ γ (s (t + i))))) hF₁).trans
    ((integral_congr_ae ?_).trans
      (hexp (fun t s a r => ((γ * ℓ) ^ (id : ℕ → ℕ)) @
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) hFθ).symm)
  filter_upwards [hpt] with ω h
  refine tsum_congr fun t => ?_
  rw [h t, hδθ (fun j => s j ω) (fun j => r j ω) t]


-- created on 2026-10-21
