import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.StronglyMeasurable_Eq12
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Finset Real
set_option maxHeartbeats 800000


attribute [local instance] Classical.propDecidable

/-- Indicator of a fixed state, integrated against `stageK θ x`, is `1{x = y}`. -/
private lemma integral_stageK_eq
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (x y : 𝒮) :
-- imply
  ∫ w, (if w.2.1 = y then (1 : ℝ) else 0) ∂(M.stageK θ x) =
    if x = y then (1 : ℝ) else 0 := by
-- proof
  have := M.env.reward_markov
  let f : ℝ × 𝒮 × 𝒜 → ℝ := fun w => if w.2.1 = y then (1 : ℝ) else 0
  have hf : StronglyMeasurable f := Real.StronglyMeasurable_Eq12 y
  have hC : ∀ w, ‖f w‖ ≤ (1 : ℝ) := fun w => by
    simp [f]
    split_ifs <;> simp
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ x
  have hinner : ∀ u, ∫ ρ, f (ρ, x, u) ∂(M.env.reward (x, u)) =
    if x = y then (1 : ℝ) else 0 := by
    intro u
    have : IsProbabilityMeasure (M.env.reward (x, u)) := inferInstance
    have hconst : (fun ρ : ℝ => f (ρ, x, u)) = fun _ => if x = y then (1 : ℝ) else 0 := by
      funext ρ
      simp [f]
    rw [hconst, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul]
  change ∫ z, f z ∂(M.stageK θ x) = _
  rw [e]
  simp_rw [smul_eq_mul, hinner]
  if hxy : x = y then
    simpa [hxy] using M.policy.integral_eq_one θ y
  else
    simp [hxy]

/-- One-step occupancy through `x`:
`∫ z, T(z.s, z.a){y} ∂(stageK θ x) = ∫ u, π(u | x) * T(x, u){y} ∂ref`. -/
private lemma integral_trans_real_stageK
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (x y : 𝒮) :
-- imply
  ∫ z, (M.env.trans z.2).real {y} ∂(M.stageK θ x) =
    ∫ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y} ∂ReferenceMeasure.measure := by
-- proof
  have := M.env.reward_markov
  have := M.env.trans_markov
  let f : ℝ × 𝒮 × 𝒜 → ℝ := fun z => (M.env.trans z.2).real {y}
  have hf : StronglyMeasurable f := by
    have hμ : Measurable fun p : 𝒮 × 𝒜 => (M.env.trans p).real {y} :=
      ENNReal.measurable_toReal.comp
        ((Measure.measurable_coe (measurableSet_singleton y)).comp M.env.trans.measurable)
    exact (hμ.comp measurable_snd).stronglyMeasurable
  have hC : ∀ z, ‖f z‖ ≤ (1 : ℝ) := fun z => by
    have : IsProbabilityMeasure (M.env.trans z.2) := inferInstance
    have hnonneg : (0 : ℝ) ≤ (M.env.trans z.2).real {y} := measureReal_nonneg
    have hle : (M.env.trans z.2).real {y} ≤ 1 := measureReal_le_one
    simp [f, Real.norm_eq_abs, abs_of_nonneg hnonneg, hle]
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ x
  have hinner : ∀ u, ∫ ρ, f (ρ, x, u) ∂(M.env.reward (x, u)) =
    (M.env.trans (x, u)).real {y} := by
    intro u
    have : IsProbabilityMeasure (M.env.reward (x, u)) := inferInstance
    have hconst : (fun ρ : ℝ => f (ρ, x, u)) = fun _ => (M.env.trans (x, u)).real {y} := by
      funext ρ
      simp [f]
    rw [hconst, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul]
  change ∫ z, f z ∂(M.stageK θ x) = _
  rw [e]
  simp_rw [smul_eq_mul, hinner]

/--
Reachability: if `ℙ(s[t] = x) ≠ 0` and `∫ u, π(u | x) * T(x, u){y} ∂ref ≠ 0`,
then `ℙ(s[t+1] = y) ≠ 0`.
-/
private lemma RealPreimageS_succ
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x y : 𝒮}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (hμ : ∫ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y} ∂ReferenceMeasure.measure ≠ 0) :
-- imply
  (M θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 := by
-- proof
  have := M.env.trans_markov
  let f : ℝ × 𝒮 × 𝒜 → ℝ := fun w => if w.2.1 = y then (1 : ℝ) else 0
  have hf : StronglyMeasurable f := Real.StronglyMeasurable_Eq12 y
  have hC : ∀ w, ‖f w‖ ≤ (1 : ℝ) := fun w => by
    simp [f]
    split_ifs <;> simp
  have hE :
    ∫ ω, (if s t ω = x then (1 : ℝ) else 0) * f (ω (t + 1)) ∂(M θ) =
      (M θ).real (s t ⁻¹' {x}) *
        ∫ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y} ∂ReferenceMeasure.measure := by
    have hw :=
      Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) h₀ hf hC θ t 1 x
    have hKf :=
      Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ 0
    have hK : ∀ z, M.Kf θ f 1 z =
      ∫ y', (∫ w, f w ∂(M.stageK θ y')) ∂(M.env.trans z.2) := fun z => by
      simpa [DensityModel.Kf] using hKf z
    have hy' : ∀ y', ∫ w, f w ∂(M.stageK θ y') = if y' = y then (1 : ℝ) else 0 :=
      fun y' => integral_stageK_eq (M := M) θ y' y
    apply hw.trans
    refine congrArg (fun z => (M θ).real (s t ⁻¹' {x}) * z) ?_
    trans ∫ z, (M.env.trans z.2).real {y} ∂(M.stageK θ x)
    ·
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      rw [hK]
      simp_rw [hy']
      have : IsProbabilityMeasure (M.env.trans z.2) := inferInstance
      have hfun : (fun y' : 𝒮 => if y' = y then (1 : ℝ) else 0) =
        ({y} : Set 𝒮).indicator (fun _ => (1 : ℝ)) := by
        funext y'
        by_cases hyy : y' = y <;> simp [hyy, Set.indicator]
      rw [hfun, integral_indicator (measurableSet_singleton y), MeasureTheory.setIntegral_const,
        smul_eq_mul, mul_one]
    ·
      exact integral_trans_real_stageK (M := M) θ x y
  have hpos :
    0 < (M θ).real (s t ⁻¹' {x}) *
      ∫ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y} ∂ReferenceMeasure.measure := by
    have hx : 0 < (M θ).real (s t ⁻¹' {x}) :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hP)
    refine mul_pos hx (lt_of_le_of_ne ?_ (Ne.symm hμ))
    exact integral_nonneg fun u =>
      mul_nonneg (M.policy.nonneg θ x u) measureReal_nonneg
  have hle :
    ∫ ω, (if s t ω = x then (1 : ℝ) else 0) * f (ω (t + 1)) ∂(M θ) ≤
      (M θ).real (s (t + 1) ⁻¹' {y}) := by
    have hs1 : Measurable (s (t + 1)) := Random.Measurable.of.All_Eq.snd.fst h₀ (t + 1)
    have hset : MeasurableSet (s (t + 1) ⁻¹' {y}) := hs1 (measurableSet_singleton y)
    have hrew : (fun ω => (if s t ω = x then (1 : ℝ) else 0) * f (ω (t + 1))) =
      fun ω => (if s t ω = x then (1 : ℝ) else 0) *
        (if s (t + 1) ω = y then (1 : ℝ) else 0) := by
      funext ω
      obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
        funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
      simp [f]
    have hpt : ∀ ω, (if s (t + 1) ω = y then (1 : ℝ) else 0) =
      (s (t + 1) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) ω := fun ω => by
      simp [Set.indicator]
    rw [hrew]
    simp_rw [hpt]
    refine (integral_mono ?_ ((integrable_const (1 : ℝ)).indicator hset) fun ω => ?_).trans_eq ?_
    ·
      have hm : Measurable fun ω =>
        (if s t ω = x then (1 : ℝ) else 0) *
          (s (t + 1) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) ω := by
        have hs0 : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₀ t
        have hindm : Measurable fun ω =>
          (s (t + 1) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) ω :=
          measurable_const.indicator hset
        exact (Measurable.ite (hs0 (measurableSet_singleton x)) measurable_const
          measurable_const).mul hindm
      exact Integrable.of_bound hm.aestronglyMeasurable (1 : ℝ)
        (Filter.Eventually.of_forall fun ω => by
          by_cases h1 : s t ω = x <;> by_cases h2 : ω ∈ s (t + 1) ⁻¹' {y} <;>
            simp [h1, h2, Set.indicator])
    · by_cases h1 : s t ω = x <;> by_cases h2 : ω ∈ s (t + 1) ⁻¹' {y} <;>
        simp [h1, h2, Set.indicator]
    · rw [integral_indicator hset, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  intro h0
  rw [h0, hE] at hle
  exact (not_le_of_gt hpos) hle

/--
Observational Bellman gradient on a reachable state (`ℙ(s[t] = x) ≠ 0`):
`fderiv V(t, x) = ∫ (rkd + γ ∫ V0) • fderiv π ∂ref + γ • ∫ π • ∫ fderiv V(t+1) ∂T ∂ref`.
Time-`t` form of
[fderiv V0](?module=Random.Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob)
(`bellmanFderivClosed`), with the next-state derivative taken on the observational `V(t+1)`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {t : ℕ}
  {x : 𝒮}
  {θ : Θ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (hg : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (hsup : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞)
  (h₃ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  fderiv ℝ (fun θ' => M.V θ' γ t x) θ =
    ∫ u, (M.rkd x u + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u))) •
      fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ ∂ReferenceMeasure.measure +
      γ • ∫ u, (M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.env.trans (x, u)))
          ∂ReferenceMeasure.measure := by
-- proof
  have := M.env.trans_markov
  obtain ⟨Cg, hCg⟩ := id hsup
  have hCg' : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg := fun x => hCg ⟨x, rfl⟩
  have hCπ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using h₂ θ x u
  rw [Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
    (M := M) hγ h₀ hπ h₁ hCπ hg hsup h₃]
  rw [bellmanFderivClosed (M := M) h₁ h₂ hg hsup hγ hπ x θ]
  congr 1
  refine congrArg (fun z => γ • z) ?_
  let FV0 : 𝒮 → Θ →L[ℝ] ℝ := fun y => fderiv ℝ (fun θ' => M.V0 θ' γ y) θ
  let FV : 𝒮 → Θ →L[ℝ] ℝ := fun y => fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ
  have hπint : Integrable (fun u => M.policy.prob θ x u) ReferenceMeasure.measure :=
    integrable_of_integral_eq_one (M.policy.integral_eq_one θ x)
  have hμint : ∀ y, Integrable (fun u =>
    M.policy.prob θ x u * (M.env.trans (x, u)).real {y}) ReferenceMeasure.measure := fun y => by
    have hm : Measurable fun u => (M.env.trans (x, u)).real {y} :=
      ENNReal.measurable_toReal.comp
        ((Measure.measurable_coe (measurableSet_singleton y)).comp
          (M.env.trans.measurable.comp measurable_prodMk_left))
    have hπm : Measurable fun u => M.policy.prob θ x u :=
      (hπ θ).comp measurable_prodMk_left
    exact Integrable.mono hπint (hπm.mul hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        have : IsProbabilityMeasure (M.env.trans (x, u)) := inferInstance
        have hnn : (0 : ℝ) ≤ (M.env.trans (x, u)).real {y} := measureReal_nonneg
        have hle : (M.env.trans (x, u)).real {y} ≤ 1 := measureReal_le_one
        have hπn : (0 : ℝ) ≤ M.policy.prob θ x u := M.policy.nonneg θ x u
        simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg hπn, abs_of_nonneg hnn]
        exact mul_le_of_le_one_right hπn hle)
  have hswap : ∀ F : 𝒮 → Θ →L[ℝ] ℝ,
    ∫ u, (M.policy.prob θ x u • (∫ y, F y ∂(M.env.trans (x, u)))) ∂ReferenceMeasure.measure =
      ∑ y, (∫ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y} ∂ReferenceMeasure.measure) •
        F y := by
    intro F
    have hfin : ∀ u, ∫ y, F y ∂(M.env.trans (x, u)) =
      ∑ y : 𝒮, (M.env.trans (x, u)).real {y} • F y := fun u => by
      rw [integral_fintype Integrable.of_finite]
    simp_rw [hfin]
    have hsum :
      (fun u => M.policy.prob θ x u • ∑ y : 𝒮, (M.env.trans (x, u)).real {y} • F y) =
        fun u => ∑ y : 𝒮, (M.policy.prob θ x u * (M.env.trans (x, u)).real {y}) • F y := by
      funext u
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_smul]
    rw [hsum]
    have hF : ∀ y, Integrable (fun u =>
      (M.policy.prob θ x u * (M.env.trans (x, u)).real {y}) • F y) ReferenceMeasure.measure :=
      fun y => (hμint y).smul_const (F y)
    rw [integral_finsetSum (s := Finset.univ) (fun y _ => hF y)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_smul_const]
  rw [hswap FV0, hswap FV]
  refine Finset.sum_congr rfl fun y _ => ?_
  let μy := ∫ u, M.policy.prob θ x u * (M.env.trans (x, u)).real {y} ∂ReferenceMeasure.measure
  change μy • FV0 y = μy • FV y
  if hμ : μy = 0 then
    simp [hμ]
  else
    have hy : (M θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 :=
      RealPreimageS_succ (M := M) h₀ h₃ hμ
    have hfd :=
      Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
        (M := M) hγ h₀ hπ h₁ hCπ hg hsup hy
    simp [FV0, FV, hfd]


-- created on 2026-11-13
