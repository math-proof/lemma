import Lemma.Random.Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.MeasurableRkd
import Lemma.Random.NormRkd.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real


instance instPSpace_policy_id
  {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} (κ : Θ) (x : 𝒮) :
  PSpace (M.policy.kernel κ x) (id : 𝒜 → 𝒜) :=
  ⟨measurable_id.aemeasurable⟩

instance instPSpace_policy_asRV_id
  {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} (κ : Θ) (x : 𝒮) :
  PSpace (M.policy.kernel κ x) (Expectation.asRV (id : 𝒜 → 𝒜)) :=
  ⟨measurable_id.aemeasurable⟩


private noncomputable def mirror
  {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  (M : DensityModel Θ 𝒮 𝒜) (𝔇 : Θ → Θ → 𝒮 → ℝ)
  (θ_π θ_bar : Θ) (γ : ℝ) (x : 𝒮) : ℝ :=
  let a : 𝒜 → 𝒜 := id
  have : PSpace (M.policy.kernel θ_bar x) (Expectation.asRV a) :=
    ⟨(measurable_id : Measurable a).aemeasurable⟩
  𝔼[a : M.policy.kernel θ_bar x](M.rkd x a + γ * ∫ y, M.V0 θ_π γ y ∂(M.env.trans (x, a))) - 𝔇 θ_π θ_bar x


/--
Lemma 3.3 of Kuba et al., [Mirror Learning](https://arxiv.org/pdf/2201.02373),
and its corollary on the expected return `η(π) = 𝔼_{s∼d}[V_π(s)]`,
where `d` is the initial-state law `M.env.init`.

The mirror operator is the official one from the body of the paper,
`[ℳ^{π̄}_𝔇 Q_θ](x) = 𝔼_{a∼π̄}[Q_θ(x, a)] - 𝔇_θ(π̄|x)`,
where `Q_θ` is the closed-form action value
`rkd x u + γ * ∫ y, V0 θ γ y ∂T(· | x, u)`.
The density ratio `ν/β` appears only in the Appendix B algebra and in the
Monte-Carlo estimator (6), not in this operator.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Nonempty 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ θ' : Θ}
  {γ : ℝ}
  {𝔇 : Θ → Θ → 𝒮 → ℝ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (hD0 : ∀ x, 𝔇 θ θ x = 0)
  (hD : ∀ x, 0 ≤ 𝔇 θ θ' x)
  (hℳ : ∀ x, mirror M 𝔇 θ θ' γ x ≥ mirror M 𝔇 θ θ γ x) :
-- imply
  (∀ x, M.V0 θ' γ x ≥ M.V0 θ γ x) ∧
    (∫ x, M.V0 θ' γ x ∂M.env.init ≥ ∫ x, M.V0 θ γ x ∂M.env.init) := by
-- proof
  have := M.env.trans_markov
  have := M.env.init_prob
  have hπm : ∀ κ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob κ z.1 z.2) :=
    M.policy.measurable_prob
  have hV : ∀ κ, Measurable (M.V0 κ γ) := fun κ =>
    Measurable_Vkd.of.All_Measurable_Prob (M := M) hπm κ γ
  have hBound : ∀ κ x, ‖M.V0 κ γ x‖ ≤ (1 - γ)⁻¹ * |M.env.R| := fun κ x =>
    NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) hγ κ x
  have hIntBound : ∀ {f : 𝒮 → ℝ} {C : ℝ} (x : 𝒮) (u : 𝒜),
      (∀ y, ‖f y‖ ≤ C) → ‖∫ y, f y ∂(M.env.trans (x, u))‖ ≤ C := by
    intro f C x u hf
    simpa [probReal_univ] using
      norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
        (Filter.Eventually.of_forall hf)
  let T (κ : Θ) (x : 𝒮) (u : 𝒜) : ℝ :=
    ∫ y, M.V0 κ γ y ∂(M.env.trans (x, u))
  let Q (κ : Θ) (x : 𝒮) (u : 𝒜) : ℝ :=
    M.rkd x u + γ * T κ x u
  let backup (κ_π κ_bar : Θ) (x : 𝒮) : ℝ :=
    ∫ u, M.policy.prob κ_bar x u * Q κ_π x u ∂ReferenceMeasure.measure
  have hπI : ∀ κ x, Integrable (M.policy.prob κ x) ReferenceMeasure.measure := by
    intro κ x
    apply Integrable.of_integral_ne_zero
    simp [M.policy.integral_eq_one κ x]
  have hπu : ∀ κ x, Measurable (M.policy.prob κ x) :=
    fun κ x => (hπm κ).comp measurable_prodMk_left
  have hT : ∀ κ x, Measurable (T κ x) :=
    fun κ x =>
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z => M.V0 κ γ z.2)
        ((hV κ).stronglyMeasurable.comp_measurable measurable_snd)).measurable).comp
        measurable_prodMk_left
  have hQmeas : ∀ κ x, Measurable (Q κ x) := fun κ x =>
    ((MeasurableRkd (M := M)).comp measurable_prodMk_left).add
      (measurable_const.mul (hT κ x))
  have hmulI : ∀ {κ : Θ} {g : 𝒜 → ℝ} {C : ℝ} (x : 𝒮),
      Measurable g →
        (∀ u, ‖g u‖ ≤ C) →
          Integrable (fun u => M.policy.prob κ x u * g u)
            ReferenceMeasure.measure := by
    intro κ g C x hg hgC
    apply ((hπI κ x).mul_const _).mono'
    · exact ((hπu κ x).mul hg).aestronglyMeasurable
    ·
      apply Filter.Eventually.of_forall
      intro u
      rw [norm_mul, Real.norm_of_nonneg (M.policy.nonneg κ x u)]
      exact mul_le_mul_of_nonneg_left (hgC u) (M.policy.nonneg κ x u)
  have hQI : ∀ κ_π κ_bar x,
      Integrable (fun u => M.policy.prob κ_bar x u * Q κ_π x u)
        ReferenceMeasure.measure := by
    intro κ_π κ_bar x
    apply hmulI (C := |M.env.R| + |γ| * ((1 - γ)⁻¹ * |M.env.R|)) x
      (hQmeas κ_π x)
    intro u
    have hR := NormRkd.le.Abs_R (M := M) x u
    have hVint := hIntBound (x := x) (u := u) (hBound κ_π)
    calc
      _ ≤ ‖M.rkd x u‖ + ‖γ * T κ_π x u‖ :=
        norm_add_le _ _
      _ = ‖M.rkd x u‖ + |γ| * ‖T κ_π x u‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ |M.env.R| + |γ| * ((1 - γ)⁻¹ * |M.env.R|) :=
        add_le_add (by simpa [Real.norm_eq_abs] using hR)
          (mul_le_mul_of_nonneg_left hVint (abs_nonneg _))
  have hE : ∀ κ_π κ_bar x,
      Expectation.ofRV (M.policy.kernel κ_bar x) (id : 𝒜 → 𝒜) (Q κ_π x) = backup κ_π κ_bar x := by
    intro κ_π κ_bar x
    simp only [Expectation.ofRV, expectation_real, Measure.map_id]
    have hdens : Measurable (M.policy.dens κ_bar x) :=
      (M.policy.measurable_dens κ_bar).comp
        (Measurable.prodMk measurable_const measurable_id)
    have hker : M.policy.kernel κ_bar x =
        (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens κ_bar x) :=
      Kernel.withDensity_apply
        (Kernel.const 𝒮 (ReferenceMeasure.measure : Measure 𝒜))
        (M.policy.measurable_dens κ_bar) x
    rw [hker, integral_withDensity_eq_integral_toReal_smul hdens
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [DensityPolicy.dens, ENNReal.toReal_ofReal (M.policy.nonneg κ_bar x u)]
  have hVQ : ∀ κ x, M.V0 κ γ x = backup κ κ x := by
    intro κ x
    have hBell :=
      Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob (M := M) hπm hγ κ x
    have hr : Integrable (fun u => M.policy.prob κ x u * M.rkd x u)
        ReferenceMeasure.measure :=
      hmulI x ((MeasurableRkd (M := M)).comp measurable_prodMk_left)
        fun u => NormRkd.le.Abs_R (M := M) x u
    have hc : Integrable (fun u => M.policy.prob κ x u * T κ x u)
        ReferenceMeasure.measure :=
      hmulI x (hT κ x) fun u => hIntBound x u (hBound κ)
    have hsum :
      ∫ u, M.policy.prob κ x u * M.rkd x u ∂ReferenceMeasure.measure +
          ∫ u, γ * (M.policy.prob κ x u * T κ x u) ∂ReferenceMeasure.measure =
        ∫ u, M.policy.prob κ x u * Q κ x u ∂ReferenceMeasure.measure := by
      rw [← integral_add hr (hc.const_mul γ)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      simp only [Q]
      ring
    rw [hBell, ← integral_const_mul, hsum]
  let Δ : 𝒮 → ℝ := fun x => M.V0 θ' γ x - M.V0 θ γ x
  let TΔ (x : 𝒮) (u : 𝒜) : ℝ := ∫ y, Δ y ∂(M.env.trans (x, u))
  have hΔm : Measurable Δ := (hV θ').sub (hV θ)
  have hΔb : ∀ y, ‖Δ y‖ ≤ 2 * ((1 - γ)⁻¹ * |M.env.R|) := by
    intro y
    apply (norm_sub_le _ _).trans
    have := add_le_add (hBound θ' y) (hBound θ y)
    simpa [two_mul] using this
  have hΔbb : BddBelow (Set.range Δ) := by
    refine ⟨-(2 * ((1 - γ)⁻¹ * |M.env.R|)), ?_⟩
    rintro _ ⟨y, rfl⟩
    apply (abs_le.mp _).1
    simpa [Real.norm_eq_abs] using hΔb y
  let infΔ : ℝ := ⨅ y, Δ y
  have hI : ∀ x,
      ∫ u, M.policy.prob θ' x u * TΔ x u ∂ReferenceMeasure.measure ≥
        infΔ := by
    intro x
    have hinner : ∀ u, TΔ x u ≥ infΔ := fun u => by
      have hInt : Integrable Δ (M.env.trans (x, u)) :=
        Integrable.of_bound hΔm.aestronglyMeasurable _
          (Filter.Eventually.of_forall hΔb)
      calc
        _ ≥ ∫ y, infΔ ∂(M.env.trans (x, u)) :=
          integral_mono (integrable_const _) hInt (fun y => ciInf_le hΔbb y)
        _ = infΔ := by
          simp
    have hTΔ : Measurable (TΔ x) :=
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z => Δ z.2)
        (hΔm.stronglyMeasurable.comp_measurable measurable_snd)).measurable).comp
        measurable_prodMk_left
    have hc : Integrable (fun u => M.policy.prob θ' x u * TΔ x u)
        ReferenceMeasure.measure :=
      hmulI x hTΔ fun u => hIntBound x u hΔb
    have hconst : Integrable (fun u => M.policy.prob θ' x u * infΔ)
        ReferenceMeasure.measure :=
      (hπI θ' x).mul_const _
    calc
      _ ≥ ∫ u, M.policy.prob θ' x u * infΔ ∂ReferenceMeasure.measure :=
        integral_mono hconst hc (fun u =>
          mul_le_mul_of_nonneg_left (hinner u) (M.policy.nonneg θ' x u))
      _ = ∫ u, infΔ * M.policy.prob θ' x u ∂ReferenceMeasure.measure :=
        integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
      _ = infΔ * ∫ u, M.policy.prob θ' x u ∂ReferenceMeasure.measure :=
        integral_const_mul infΔ (M.policy.prob θ' x)
      _ = infΔ := by
        rw [M.policy.integral_eq_one θ' x, mul_one]
  have hleft : ∀ x, Δ x ≥ γ * infΔ := by
    intro x
    let I : ℝ :=
      ∫ u, M.policy.prob θ' x u * TΔ x u ∂ReferenceMeasure.measure
    have hsub :
      backup θ' θ' x - backup θ θ' x =
        ∫ u, M.policy.prob θ' x u * (Q θ' x u - Q θ x u)
          ∂ReferenceMeasure.measure := by
      rw [← integral_sub (hQI θ' θ' x) (hQI θ θ' x)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      ring
    have hQΔ : ∀ u, Q θ' x u - Q θ x u = γ * TΔ x u := by
      intro u
      have hIntV (κ : Θ) : Integrable (M.V0 κ γ) (M.env.trans (x, u)) :=
        Integrable.of_bound (hV κ).aestronglyMeasurable _
          (Filter.Eventually.of_forall (hBound κ))
      calc
        _ = M.rkd x u + γ * T θ' x u - (M.rkd x u + γ * T θ x u) :=
          rfl
        _ = γ * T θ' x u - γ * T θ x u := by
          ring
        _ = γ * (T θ' x u - T θ x u) := by
          ring
        _ = γ * TΔ x u := by
          simp only [T, TΔ, Δ]
          rw [← integral_sub (hIntV θ') (hIntV θ)]
    have hγI : backup θ' θ' x - backup θ θ' x = γ * I := by
      rw [hsub, ← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp
      rw [hQΔ u]
      ring
    have hsplit : Δ x = γ * I + (backup θ θ' x - backup θ θ x) := by
      change M.V0 θ' γ x - M.V0 θ γ x = _
      rw [hVQ θ' x, hVQ θ x, sub_eq_iff_eq_add.mp hγI]
      ring
    have hpen : 𝔇 θ θ' x ≤ backup θ θ' x - backup θ θ x := by
      have hx :
        Expectation.ofRV (M.policy.kernel θ' x) (id : 𝒜 → 𝒜) (Q θ x) - 𝔇 θ θ' x ≥
          Expectation.ofRV (M.policy.kernel θ x) (id : 𝒜 → 𝒜) (Q θ x) - 𝔇 θ θ x := by
        simpa [mirror, Expectation.asRV, Q, T] using hℳ x
      rw [hE θ θ' x, hE θ θ x] at hx
      simp [hD0 x, sub_zero] at hx
      exact le_sub_comm.mp hx
    calc
      _ = γ * I + (backup θ θ' x - backup θ θ x) :=
        hsplit
      _ ≥ γ * I + 𝔇 θ θ' x :=
        (add_le_add (le_refl (γ * I)) hpen).ge
      _ ≥ γ * I :=
        (le_add_of_nonneg_right (hD x)).ge
      _ ≥ γ * infΔ :=
        (mul_le_mul_of_nonneg_left (hI x) hγ.1).ge
  have hinf : 0 ≤ infΔ := by
    apply (mul_nonneg_iff_of_pos_left (sub_pos.mpr hγ.2)).mp
    convert sub_nonneg.mpr (le_ciInf fun x => hleft x)
    ring
  have hVge : ∀ x, M.V0 θ' γ x ≥ M.V0 θ γ x := fun x =>
    sub_nonneg.mp (le_trans hinf (ciInf_le hΔbb x))
  refine And.intro hVge ?_
  have hInt (κ : Θ) : Integrable (M.V0 κ γ) M.env.init :=
    Integrable.of_bound (hV κ).aestronglyMeasurable _
      (Filter.Eventually.of_forall (hBound κ))
  exact integral_mono (hInt θ) (hInt θ') hVge


-- created on 2023-04-20
-- updated on 2026-11-12
