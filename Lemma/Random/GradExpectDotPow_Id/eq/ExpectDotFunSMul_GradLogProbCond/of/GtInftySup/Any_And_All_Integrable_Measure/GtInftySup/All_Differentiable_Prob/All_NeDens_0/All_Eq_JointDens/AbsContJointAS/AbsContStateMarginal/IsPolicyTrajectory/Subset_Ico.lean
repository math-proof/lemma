import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
import Lemma.Real.MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.EqProb
import Theorem.Probability.CondExpectation
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open Finset (range)
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real IsPolicyTrajectory
set_option maxHeartbeats 900000


/--
Generalized advantage estimation with the paper's weighted-average estimator (Schulman et al.,
arXiv 1506.02438, Eq. (16)) for continuous actions. `V` is the textbook (observation) form
of the conditional expected return,
`V[t] «s»[t] = 𝔼[r: M θ]((γ ^ id) ⬝ᵥ r[t:] | s[t] = «s»[t])`. Path-GAE is built from the
path-value `V_δ[t] δ k = V[t + k] (δ k)`. With TD residuals
`δ[j] = r[j] + γ * V[j + 1] s[j + 1] - V[j] s[j]` and `{γ, ℓ} ⊆ Ico 0 1`, the exponentially
weighted average `(1 - ℓ) * ((ℓ ^ id) ⬝ᵥ fun k ↦ (γ ^ range(k+1)) ⬝ᵥ δ)` equals the closed
form, via `Real.MulSub1_Dot_FunDotPow_Range.…Subset_Ico`, applying the continuous closed-form GAE.

`IsConditionalProbability` supplies `IsPolicyTrajectory`, `AbsContJointAS`, and
`M.policy.prob θ x u = (ℙ[M θ]((a t) = u | (s t) = x) : ℝ)`. Fun binders `ℕ ⇀ 𝒮` / `ℕ ⇀ 𝒜`
appear as `s[t] = «\sf{s}»[t]` / `a[t] = «\sf{a}»[t]`. The score is
`∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log` under `𝔼[r, s, a : M θ]`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {V : ℕ ⇀ 𝒮 → ℝ}
-- given
  (h₀ : {γ, ℓ} ⊆ Set.Ico 0 1)
  (hfactor : DensityModel.IsConditionalProbability M r s a)
  (h₁ : ∀ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)))
  (h₂ : ∃ (g : 𝒮 → 𝒜 → ℝ),
    (∀ θ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
      ‖∇[θ] (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)‖ ≤
        g «\sf{s}»[t] «\sf{a}»[t]) ∧
    (∀ x, Integrable (g x) ReferenceMeasure.measure) ∧
    (sup[x] (∫ u, g x u ∂ReferenceMeasure.measure) < ∞))
  (hφ : StronglyMeasurable
    (fun ((s0, a0) : 𝒮 × 𝒜) => ∇[θ] (ℙ[M θ](a[0] = a0 | s[0] = s0) : ℝ).log))
  (hMs : sup[«\sf{s}» : ℕ ⇀ 𝒮, «\sf{a}» : ℕ ⇀ 𝒜]
    ‖∇[θ] (ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ).log‖ < ∞)
  (hV : ∀ t («\sf{s}» : ℕ ⇀ 𝒮),
    V[t] «\sf{s}»[t] =
      𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = «\sf{s}»[t])) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun θ t =>
    hfactor.htr.singlePSpace_as (haj := hfactor.haj) θ t
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(hfactor.htr.measurable_r t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(hfactor.htr.measurable_s t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(hfactor.htr.measurable_a t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_δ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun t δ k => V[t + k] (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      (((1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
        (r[t:] + γ • V_δ[t + 1] s[t + 1:] - V_δ[t] s[t:]))) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  intro hPas _ _ _ _ V_δ
  have hπeq : ∀ θ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
      (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ) =
        M.policy.prob θ «\sf{s}»[t] «\sf{a}»[t] := fun θ t sb ab =>
    (hfactor.factor θ t (sb t) (ab t)).symm
  simp only [FinsetPow.dot_eq]
  classical
  have hγ : γ ∈ Set.Ico 0 1 := h₀ (by simp)
  have hℓ₀ : ℓ ∈ Set.Ico 0 1 := h₀ (by simp)
  have hℓ : ℓ ∈ Set.Icc 0 1 := ⟨hℓ₀.1, hℓ₀.2.le⟩
  have hπ : ∀ θ', Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ' z.1 z.2) :=
    M.policy.measurable_prob
  obtain ⟨g, ⟨h₃bound, ⟨h₄, h₅sup⟩⟩⟩ := h₂
  obtain ⟨Cg, h₅UB⟩ := h₅sup
  have h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg := fun x =>
    h₅UB (Set.mem_range_self x)
  have hφpol : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)) := by
    convert hφ using 1
    funext z
    refine congrArg (gradient · θ) ?_
    funext θ'
    simp only [hπeq θ' 0 ⟨fun _ => z.1⟩ ⟨fun _ => z.2⟩]
  obtain ⟨Ms, hMsUB⟩ := hMs
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (hfactor.htr.stage_eq t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (hfactor.htr.stage_eq t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (hfactor.htr.stage_eq t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  let : BorelSpace Θ := ⟨rfl⟩
  have h₁' : ∀ t, (· t) = (r t, s t, a t) := fun t => by
    funext ω; rfl
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst h₁' t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁' t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁' t).aemeasurable⟩)
  have : ∀ θ' t, SinglePSpace (M θ') (a t, s t) := fun θ' t =>
    hfactor.htr.singlePSpace_as (haj := hfactor.haj) θ' t
  have hscore : ∀ t (x : 𝒮) (u : 𝒜),
      gradient (fun θ' : Θ => Real.log (M.policy.prob θ' x u)) θ =
        gradient (fun θ' : Θ => (ℙ[M θ']((a t) = u | (s t) = x) : ℝ).log) θ := by
    intro t x u
    have hfe : (fun θ' : Θ => Real.log (M.policy.prob θ' x u)) =
        (fun θ' : Θ => (ℙ[M θ']((a t) = u | (s t) = x) : ℝ).log) :=
      funext fun θ' =>
        congrArg Real.log (hπeq θ' t ⟨fun _ => x⟩ ⟨fun _ => u⟩).symm
    simp only [hfe]
  have hφg : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => gradient (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ) :=
    hφpol
  have hφgℙ : ∀ t, StronglyMeasurable fun z : 𝒮 × 𝒜 =>
      gradient (fun θ' : Θ => (ℙ[M θ']((a t) = z.2 | (s t) = z.1) : ℝ).log) θ := fun t => by
    convert hφg using 1
    funext z
    exact (hscore t z.1 z.2).symm
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
    r k ω + γ * V[k + 1] (s (k + 1) ω) - V[k] (s k ω) := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₁' k).add
      (((measurable_of_countable (V[k + 1])).comp
          (Random.Measurable.of.All_Eq.snd.fst h₁' (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (V[k])).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁' k))
  have hrm : ∀ n, Measurable (r n) := fun n =>
    Random.Measurable.of.All_Eq.fst h₁' n
  have hsm : ∀ n, Measurable (s n) := fun n =>
    Random.Measurable.of.All_Eq.snd.fst h₁' n
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfG : ∀ n, Measurable
      (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:]) := fun n =>
    Measurable.tsum fun k => (measurable_pi_apply (n + k)).const_mul _
  have hr_bd : ∀ᵐ ω ∂(M θ), ∀ j, |r j ω| ≤ |M.env.R| := by
    have hclip : ∀ j,
        r j =ᵐ[M θ] fun ω => clip (ω j).1 (-M.env.R) M.env.R := fun j =>
      MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₁' θ j
    have hclip' : ∀ᵐ ω ∂(M θ), ∀ j,
        r j ω = clip (ω j).1 (-M.env.R) M.env.R :=
      (ae_all_iff (ι := ℕ)).mpr hclip
    filter_upwards [hclip'] with ω hω j
    rw [hω j, ← Real.norm_eq_abs]
    exact NormClip.le.Abs_R (R := M.env.R) (ρ := (ω j).1)
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ n,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[n:])‖ ≤
        (1 - γ)⁻¹ * |M.env.R| := by
    have hgeo := (hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|
    filter_upwards [hr_bd] with ω hω n
    refine tsum_of_norm_bounded hgeo fun k => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) k = γ ^ k := rfl
    have hslice : (fun j => r j ω)[n:] k = r (n + k) ω := by
      simp [Function.getSliceFrom_apply]
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (n + k)) (pow_nonneg hγ.1 k)
  have hret : ∀ n, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[n:] := fun n =>
    (hfG n).comp hpR
  have hGi : ∀ n,
      Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[n:]) (M θ) :=
    fun n =>
      Integrable.of_bound (hret n).aestronglyMeasurable
        ((1 - γ)⁻¹ * |M.env.R|)
        (by filter_upwards [hret_bd] with ω hω; exact hω n)
  have hV_ae : ∀ n,
      (fun ω => V[n] (s n ω)) =ᵐ[M θ]
        Expectation.condSigma (M θ) (fun ω i => r i ω) (s n)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:]) := fun n => by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω i => r i ω) (y := s n)
        (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:])
        hpR.aemeasurable (hsm n) (hfG n).stronglyMeasurable (hGi n)
    filter_upwards [hcomp] with ω hω
    have hx := hV n ⟨fun _ => s n ω⟩
    simp only at hx hω ⊢
    exact hx.trans hω
  have hVbd : ∀ᵐ ω ∂(M θ), ∀ n, |V[n] (s n ω)| ≤ (1 - γ)⁻¹ * |M.env.R| := by
    have hcond : ∀ n, ∀ᵐ ω ∂(M θ),
        |Expectation.condSigma (M θ) (fun ω i => r i ω) (s n)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:]) ω| ≤
          (1 - γ)⁻¹ * |M.env.R| := fun n => by
      have hbd :=
        ae_bdd_norm_condExp_of_ae_bdd_norm
          (f := fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun i => r i ω)[n:])
          (m := MeasurableSpace.comap (s n) inferInstance)
          (by filter_upwards [hret_bd] with ω hω; exact hω n)
      filter_upwards [hbd] with ω h
      simpa [Expectation.condSigma, Real.norm_eq_abs] using h
    have hVeq : ∀ᵐ ω ∂(M θ), ∀ n,
        V[n] (s n ω) =
          Expectation.condSigma (M θ) (fun ω i => r i ω) (s n)
            (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:]) ω :=
      (ae_all_iff (ι := ℕ)).mpr hV_ae
    have hVnorm : ∀ᵐ ω ∂(M θ), ∀ n,
        |Expectation.condSigma (M θ) (fun ω i => r i ω) (s n)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:]) ω| ≤
          (1 - γ)⁻¹ * |M.env.R| :=
      (ae_all_iff (ι := ℕ)).mpr hcond
    filter_upwards [hVeq, hVnorm] with ω heq hnorm n
    rw [heq n]
    exact hnorm n
  have hbdd : ∀ᵐ ω ∂(M θ),
      BddAbove (Set.range fun j =>
        |r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)|) := by
    filter_upwards [hr_bd, hVbd] with ω hr hV
    refine ⟨(2 / (1 - γ)) * |M.env.R|, ?_⟩
    rintro _ ⟨j, rfl⟩
    have hγn : 0 ≤ γ := hγ.1
    have htri :
        |r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)| ≤
          |r j ω| + γ * |V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
      calc
        _ ≤ |r j ω + γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (r j ω + γ * V[j + 1] (s (j + 1) ω)) (-V[j] (s j ω))
        _ ≤ |r j ω| + |γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| :=
          add_le_add (abs_add_le _ _) (le_refl _)
        _ = |r j ω| + γ * |V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
          rw [abs_mul, abs_of_nonneg hγn]
    have hle :=
      (add_le_add (add_le_add (hr j)
        (mul_le_mul_of_nonneg_left (hV (j + 1)) hγn)) (hV j))
    have hsum :
        |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) + (1 - γ)⁻¹ * |M.env.R| =
          (2 / (1 - γ)) * |M.env.R| := by
      have hne : 1 - γ ≠ 0 := sub_ne_zero.mpr hγ.2.ne.symm
      field_simp [hne]
      ring_nf
    exact (htri.trans hle).trans (le_of_eq hsum)
  have hpt : ∀ᵐ ω ∂(M θ), ∀ t,
    (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) ω + γ * V[t + i + 1] (s (t + i + 1) ω) - V[t + i] (s (t + i) ω))) =
    ((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ
      (fun k : ℕ => r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) - V[t + k] (s (t + k) ω)) := by
    filter_upwards [hbdd] with ω hb t
    exact MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico
      (δ := ⟨fun j => r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)⟩) (t := t) h₀ hb
  have hexp : ∀ F : ℕ → (ℕ → 𝒮) → (ℕ → 𝒜) → (ℕ → ℝ) → ℝ,
    (∀ t, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 => F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω)) →
    𝔼[r, s, a : M θ](
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ (F t s a r •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) =
    ∫ ω, ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) ∂(M θ) := by
    intro F hF
    have hg := fun t : ℕ =>
      StronglyMeasurable.smul (hF t).stronglyMeasurable
        ((hφgℙ t).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁' t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁' t)))
    have hGsm : StronglyMeasurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
        ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) :=
      StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        (hg t).const_smul (γ ^ t)
    let fromPath := fun (p : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜)) =>
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
  have hF₁ : ∀ t, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
    (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) ω + γ * V[t + i + 1] (s (t + i + 1) ω) - V[t + i] (s (t + i) ω))) := fun t => by
    have htsum : Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
        (1 - ℓ) * ∑' k, ℓ ^ k * ∑ i ∈ range (k + 1), γ ^ i *
          (r (t + i) ω + γ * V[t + i + 1] (s (t + i + 1) ω) - V[t + i] (s (t + i) ω)) :=
      (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        (Finset.measurable_sum _ fun i _ => (hmeas (t + i)).const_mul _).const_mul _).const_mul _
    convert htsum
    · exact Nat.cast_one
    · rfl
  have hF₂ : ∀ t, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
    (((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ
      (fun k : ℕ => r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) - V[t + k] (s (t + k) ω))) := fun t => by
    show Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 => ∑' k, (γ * ℓ) ^ k *
      (r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) - V[t + k] (s (t + k) ω))
    exact Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k => (hmeas (t + k)).const_mul _
  have hδθ : ∀ (s : ℕ → 𝒮) (r : ℕ → ℝ) (t : ℕ),
    (fun k => r (t + k) + γ * V[t + k + 1] (s (t + k + 1)) - V[t + k] (s (t + k))) =
      r[t:] + γ • V_δ[t + 1] s[t + 1:] - V_δ[t] s[t:] := by
    intro s r t
    funext k
    have hk : t + k + 1 = t + 1 + k := by omega
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_δ,
      Function.getSliceFrom_apply, hk]
  have hFθ : ∀ t, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
    (((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ
      ((fun j => r j ω)[t:] + γ • V_δ[t + 1] (fun j => s j ω)[t + 1:] -
        V_δ[t] (fun j => s j ω)[t:])) := fun t => by
    convert hF₂ t using 1
    funext ω
    exact congrArg (fun δ => Dot.dot ((γ * ℓ) ^ (id : ℕ → ℕ)) δ)
      (hδθ (fun j => s j ω) (fun j => r j ω) t).symm
  have hV' : ∀ (k : ℕ) (x : 𝒮),
      V[k] x =
        Expectation.condEval (M θ) (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => fun i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) x := fun k x => by
    simpa using hV k ⟨fun _ => x⟩
  refine (GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
    (M := M) (θ := θ) (r := ⟨r⟩) (s := ⟨s⟩) (a := ⟨a⟩) (V := V)
    hγ hℓ hfactor hπ hV' h₁ h₃bound h₄ h₅ hφpol
    (fun sb ab => hMsUB (Set.mem_range_self (sb, ab)))).trans ?_
  symm
  have hFeq :
    (fun t (s : ℕ → 𝒮) (a : ℕ → 𝒜) (r : ℕ → ℝ) =>
        (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
          (r[t:] + γ • V_δ[t + 1] s[t + 1:] - V_δ[t] s[t:]) i)) =
      (fun t (s : ℕ → 𝒮) (a : ℕ → 𝒜) (r : ℕ → ℝ) =>
        (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
          (r (t + i) + γ * V[t + i + 1] (s (t + i + 1)) - V[t + i] (s (t + i))))) := by
    funext t s a r
    congr 1
    congr 1
    funext k
    refine Finset.sum_congr rfl fun i _ => ?_
    have hk : t + i + 1 = t + 1 + i := by omega
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_δ,
      Function.getSliceFrom_apply]
    rw [hk]
  refine (congrArg
      (fun F : ℕ → (ℕ → 𝒮) → (ℕ → 𝒜) → (ℕ → ℝ) → ℝ =>
        𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
          (F t (fun j => s j) (fun j => a j) (fun j => r j) •
            ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)))
      hFeq).trans ?_
  refine (hexp (fun t s a r => (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) + γ * V[t + i + 1] (s (t + i + 1)) - V[t + i] (s (t + i))))) hF₁).trans
    ((integral_congr_ae ?_).trans
      (hexp (fun t s a r => ((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ
        (r[t:] + γ • V_δ[t + 1] s[t + 1:] - V_δ[t] s[t:])) hFθ).symm)
  filter_upwards [hpt] with ω h
  refine tsum_congr fun t => ?_
  rw [h t, hδθ (fun j => s j ω) (fun j => r j ω) t]


-- created on 2026-10-21
-- updated on 2026-11-11
