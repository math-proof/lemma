import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.StronglyMeasurable_Eq12
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Finset Real
set_option maxHeartbeats 800000


attribute [local instance] Classical.propDecidable

/-- Indicator of a fixed state, integrated against `stageK θ x`, is `1{x = y}`. -/
private lemma integral_stageK_eq
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (sₜ y : 𝒮) :
-- imply
  ∫ w, (if w.2.1 = y then (1 : ℝ) else 0) ∂(M.stageK θ sₜ) =
    if sₜ = y then (1 : ℝ) else 0 := by
-- proof
  let f : ℝ × 𝒮 × 𝒜 → ℝ := fun w => if w.2.1 = y then (1 : ℝ) else 0
  have hf : StronglyMeasurable f := Real.StronglyMeasurable_Eq12 y
  have hC : ∀ w, ‖f w‖ ≤ (1 : ℝ) := fun w => by
    simp [f]
    split_ifs <;> simp
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ sₜ
  have hinner : ∀ u, ∫ ρ, f (ρ, sₜ, u) ∂(M.reward (sₜ, u)) =
    if sₜ = y then (1 : ℝ) else 0 := by
    intro u
    have : IsProbabilityMeasure ((M.reward (sₜ, u) : Measure ℝ)) := inferInstance
    have hconst : (fun ρ : ℝ => f (ρ, sₜ, u)) = fun _ => if sₜ = y then (1 : ℝ) else 0 := by
      funext ρ
      simp [f]
    rw [hconst, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul]
  change ∫ z, f z ∂(M.stageK θ sₜ) = _
  rw [e]
  simp_rw [smul_eq_mul, hinner]
  if hxy : sₜ = y then
    simpa [hxy] using hStoch.integral_eq_one θ y
  else
    simp [hxy]

/-- One-step occupancy through `x`:
`∫ z, T(z.s, z.a){y} ∂(stageK θ x) = ∫ u, π(u | x) * T(x, u){y} ∂ref`. -/
private lemma integral_trans_real_stageK
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (sₜ y : 𝒮) :
-- imply
  ∫ z, (M.trans z.2).toMeasure.real {y} ∂(M.stageK θ sₜ) =
    ∫ u, M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y} ∂ReferenceMeasure.measure := by
-- proof
  let f : ℝ × 𝒮 × 𝒜 → ℝ := fun z => (M.trans z.2).toMeasure.real {y}
  have hf : StronglyMeasurable f := by
    have hμ : Measurable fun p : 𝒮 × 𝒜 => (M.trans p).toMeasure.real {y} :=
      ENNReal.measurable_toReal.comp
        ((Measure.measurable_coe (measurableSet_singleton y)).comp M.transK.measurable)
    exact (hμ.comp measurable_snd).stronglyMeasurable
  have hC : ∀ z, ‖f z‖ ≤ (1 : ℝ) := fun z => by
    have : IsProbabilityMeasure ((M.trans z.2 : Measure 𝒮)) := inferInstance
    have hnonneg : (0 : ℝ) ≤ (M.trans z.2).toMeasure.real {y} := measureReal_nonneg
    have hle : (M.trans z.2).toMeasure.real {y} ≤ 1 := measureReal_le_one
    simp [f, Real.norm_eq_abs, abs_of_nonneg hnonneg, hle]
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ sₜ
  have hinner : ∀ u, ∫ ρ, f (ρ, sₜ, u) ∂(M.reward (sₜ, u)) =
    (M.trans (sₜ, u)).toMeasure.real {y} := by
    intro u
    have : IsProbabilityMeasure ((M.reward (sₜ, u) : Measure ℝ)) := inferInstance
    have hconst : (fun ρ : ℝ => f (ρ, sₜ, u)) = fun _ => (M.trans (sₜ, u)).toMeasure.real {y} := by
      funext ρ
      simp [f]
    rw [hconst, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul]
  change ∫ z, f z ∂(M.stageK θ sₜ) = _
  rw [e]
  simp_rw [smul_eq_mul, hinner]

/--
Reachability: if `ℙ(s[t] = x) ≠ 0` and `∫ u, π(u | x) * T(x, u){y} ∂ref ≠ 0`,
then `ℙ(s[t+1] = y) ≠ 0`.
-/
private lemma RealPreimageS_succ
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {sₜ y : 𝒮}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M.traj θ).real (s t ⁻¹' {sₜ}) ≠ 0)
  (hμ : ∫ u, M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y} ∂ReferenceMeasure.measure ≠ 0) :
-- imply
  (M.traj θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 := by
-- proof
  let f : ℝ × 𝒮 × 𝒜 → ℝ := fun w => if w.2.1 = y then (1 : ℝ) else 0
  have hf : StronglyMeasurable f := Real.StronglyMeasurable_Eq12 y
  have hC : ∀ w, ‖f w‖ ≤ (1 : ℝ) := fun w => by
    simp [f]
    split_ifs <;> simp
  have hE :
    ∫ ω, (if s t ω = sₜ then (1 : ℝ) else 0) * f (ω (t + 1)) ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {sₜ}) *
        ∫ u, M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y} ∂ReferenceMeasure.measure := by
    have hw :=
      Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) h₀ hf hC θ t 1 sₜ
    have hKf :=
      Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ 0
    have hK : ∀ z, M.Kf θ f 1 z =
      ∫ y', (∫ w, f w ∂(M.stageK θ y')) ∂(M.trans z.2) := fun z => by
      simpa [Model.Kf] using hKf z
    have hy' : ∀ y', ∫ w, f w ∂(M.stageK θ y') = if y' = y then (1 : ℝ) else 0 :=
      fun y' => integral_stageK_eq (M := M) θ y' y
    apply hw.trans
    refine congrArg (fun z => (M.traj θ).real (s t ⁻¹' {sₜ}) * z) ?_
    trans ∫ z, (M.trans z.2).toMeasure.real {y} ∂(M.stageK θ sₜ)
    ·
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      rw [hK]
      simp_rw [hy']
      have : IsProbabilityMeasure ((M.trans z.2 : Measure 𝒮)) := inferInstance
      have hfun : (fun y' : 𝒮 => if y' = y then (1 : ℝ) else 0) =
        ({y} : Set 𝒮).indicator (fun _ => (1 : ℝ)) := by
        funext y'
        by_cases hyy : y' = y <;> simp [hyy, Set.indicator]
      rw [hfun, integral_indicator (measurableSet_singleton y), MeasureTheory.setIntegral_const,
        smul_eq_mul, mul_one]
    ·
      exact integral_trans_real_stageK (M := M) θ sₜ y
  have hpos :
    0 < (M.traj θ).real (s t ⁻¹' {sₜ}) *
      ∫ u, M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y} ∂ReferenceMeasure.measure := by
    have hx : 0 < (M.traj θ).real (s t ⁻¹' {sₜ}) :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hP)
    refine mul_pos hx (lt_of_le_of_ne ?_ (Ne.symm hμ))
    exact integral_nonneg fun u =>
      mul_nonneg (hStoch.nonneg θ sₜ u) measureReal_nonneg
  have hle :
    ∫ ω, (if s t ω = sₜ then (1 : ℝ) else 0) * f (ω (t + 1)) ∂(M.traj θ) ≤
      (M.traj θ).real (s (t + 1) ⁻¹' {y}) := by
    have hs1 : Measurable (s (t + 1)) := Random.Measurable.of.All_Eq.snd.fst h₀ (t + 1)
    have hset : MeasurableSet (s (t + 1) ⁻¹' {y}) := hs1 (measurableSet_singleton y)
    have hrew : (fun ω => (if s t ω = sₜ then (1 : ℝ) else 0) * f (ω (t + 1))) =
      fun ω => (if s t ω = sₜ then (1 : ℝ) else 0) *
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
        (if s t ω = sₜ then (1 : ℝ) else 0) *
          (s (t + 1) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) ω := by
        have hs0 : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₀ t
        have hindm : Measurable fun ω =>
          (s (t + 1) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) ω :=
          measurable_const.indicator hset
        exact (Measurable.ite (hs0 (measurableSet_singleton sₜ)) measurable_const
          measurable_const).mul hindm
      exact Integrable.of_bound hm.aestronglyMeasurable (1 : ℝ)
        (Filter.Eventually.of_forall fun ω => by
          by_cases h1 : s t ω = sₜ <;> by_cases h2 : ω ∈ s (t + 1) ⁻¹' {y} <;>
            simp [h1, h2, Set.indicator])
    · by_cases h1 : s t ω = sₜ <;> by_cases h2 : ω ∈ s (t + 1) ⁻¹' {y} <;>
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
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {t : ℕ}
  {sₜ : 𝒮}
  {θ : Θ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₂ : sup[sₜ] (∫ u, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ u‖) ∂ReferenceMeasure.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) ReferenceMeasure.measure)
  (h₃ : (M.traj θ).real (s t ⁻¹' {sₜ}) ≠ 0) :
-- imply
  fderiv ℝ (fun θ' => M.V θ' γ t sₜ) θ =
    ∫ u, (M.rkd sₜ u + γ * ∫ y, M.V0 θ γ y ∂(M.trans (sₜ, u))) •
      fderiv ℝ (fun θ' => M.π[θ'] sₜ u) θ ∂ReferenceMeasure.measure +
      γ • ∫ u, (M.π[θ] sₜ u •
        ∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.trans (sₜ, u)))
          ∂ReferenceMeasure.measure := by
-- proof
  have h₂fderiv := h₂
  rw [Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
    (M := M) hγ h₀ hπ h₁ h₂fderiv hBdd hIntg h₃]
  rw [bellmanFderivClosed (M := M) h₁ h₂ hBdd hIntg hγ hπ sₜ θ]
  congr 1
  refine congrArg (fun z => γ • z) ?_
  let FV0 : 𝒮 → Θ →L[ℝ] ℝ := fun y => fderiv ℝ (fun θ' => M.V0 θ' γ y) θ
  let FV : 𝒮 → Θ →L[ℝ] ℝ := fun y => fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ
  have hπint : Integrable (fun u => M.π[θ] sₜ u) ReferenceMeasure.measure :=
    integrable_of_integral_eq_one (hStoch.integral_eq_one θ sₜ)
  have hμint : ∀ y, Integrable (fun u =>
    M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y}) ReferenceMeasure.measure := fun y => by
    have hm : Measurable fun u => (M.trans (sₜ, u)).toMeasure.real {y} :=
      ENNReal.measurable_toReal.comp
        ((Measure.measurable_coe (measurableSet_singleton y)).comp
          (M.transK.measurable.comp measurable_prodMk_left))
    have hπm : Measurable fun u => M.π[θ] sₜ u :=
      (hπ θ).comp measurable_prodMk_left
    exact Integrable.mono hπint (hπm.mul hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        have : IsProbabilityMeasure ((M.trans (sₜ, u) : Measure 𝒮)) := inferInstance
        have hnn : (0 : ℝ) ≤ (M.trans (sₜ, u)).toMeasure.real {y} := measureReal_nonneg
        have hle : (M.trans (sₜ, u)).toMeasure.real {y} ≤ 1 := measureReal_le_one
        have hπn : (0 : ℝ) ≤ M.π[θ] sₜ u := hStoch.nonneg θ sₜ u
        simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg hπn, abs_of_nonneg hnn]
        exact mul_le_of_le_one_right hπn hle)
  have hswap : ∀ F : 𝒮 → Θ →L[ℝ] ℝ,
    ∫ u, (M.π[θ] sₜ u • (∫ y, F y ∂(M.trans (sₜ, u)))) ∂ReferenceMeasure.measure =
      ∑ y, (∫ u, M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y} ∂ReferenceMeasure.measure) •
        F y := by
    intro F
    have hfin : ∀ u, ∫ y, F y ∂(M.trans (sₜ, u)) =
      ∑ y : 𝒮, (M.trans (sₜ, u)).toMeasure.real {y} • F y := fun u => by
      rw [integral_fintype Integrable.of_finite]
    simp_rw [hfin]
    have hsum :
      (fun u => M.π[θ] sₜ u • ∑ y : 𝒮, (M.trans (sₜ, u)).toMeasure.real {y} • F y) =
        fun u => ∑ y : 𝒮, (M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y}) • F y := by
      funext u
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_smul]
    rw [hsum]
    have hF : ∀ y, Integrable (fun u =>
      (M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y}) • F y) ReferenceMeasure.measure :=
      fun y => (hμint y).smul_const (F y)
    rw [integral_finsetSum (s := Finset.univ) (fun y _ => hF y)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_smul_const]
  rw [hswap FV0, hswap FV]
  refine Finset.sum_congr rfl fun y _ => ?_
  let μy := ∫ u, M.π[θ] sₜ u * (M.trans (sₜ, u)).toMeasure.real {y} ∂ReferenceMeasure.measure
  change μy • FV0 y = μy • FV y
  if hμ : μy = 0 then
    simp [hμ]
  else
    have hy : (M.traj θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 :=
      RealPreimageS_succ (M := M) h₀ h₃ hμ
    have hfd :=
      Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
        (M := M) hγ h₀ hπ h₁ h₂fderiv hBdd hIntg hy
    simp [FV0, FV, hfd]


-- created on 2026-11-13
-- updated on 2026-11-16
