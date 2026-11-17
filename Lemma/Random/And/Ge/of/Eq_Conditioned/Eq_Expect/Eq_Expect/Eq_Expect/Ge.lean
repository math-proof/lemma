import Lemma.Random.Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.MeasurableRkd
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.Eq_WithDensity_Pdf
import Theorem.Probability.SymbolicProbability
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


instance instPSpace_policy_id
  {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] (κ : Θ) (sₜ : 𝒮) :
  PSpace (M.kernel κ sₜ) (id : 𝒜 → 𝒜) :=
  ⟨measurable_id.aemeasurable⟩

instance instPSpace_policy_asRV_id
  {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] (κ : Θ) (sₜ : 𝒮) :
  PSpace (M.kernel κ sₜ) (Expectation.asRV (id : 𝒜 → 𝒜)) :=
  ⟨measurable_id.aemeasurable⟩


private noncomputable def mirror
  {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  (M : Model Θ 𝒮 𝒜) [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] (𝔇 : Θ → Θ → 𝒮 → ℝ)
  (θ_π θ_bar : Θ) (γ : ℝ) (sₜ : 𝒮) : ℝ :=
  let a : 𝒜 → 𝒜 := id
  have : PSpace (M.kernel θ_bar sₜ) (Expectation.asRV a) :=
    ⟨(measurable_id : Measurable a).aemeasurable⟩
  𝔼[a : M.kernel θ_bar sₜ](M.rkd sₜ a + γ * ∫ y, M.V0 θ_π γ y ∂(M.trans (sₜ, a))) - 𝔇 θ_π θ_bar sₜ


/--
Lemma 3.3 of Kuba et al., [Mirror Learning](https://arxiv.org/pdf/2201.02373),
and its corollary on the expected return `η(π) = 𝔼_{s∼d}[V_π(s)]`,
where `d` is the initial-state law `M.init`.

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
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
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
    (∫ x, M.V0 θ' γ x ∂(M.init : Measure _) ≥ ∫ x, M.V0 θ γ x ∂(M.init : Measure _)) := by
-- proof
  have hπm : ∀ κ, Measurable (fun z : 𝒮 × 𝒜 => M.π[κ] z.1 z.2) :=
    hStoch.measurable_π
  have hV : ∀ κ, Measurable (M.V0 κ γ) := fun κ =>
    Measurable_Vkd.of.All_Measurable_Prob (M := M) hπm κ γ
  have hBound : ∀ κ x, ‖M.V0 κ γ x‖ ≤ (1 - γ)⁻¹ * |M.R| := fun κ x =>
    NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) hγ κ x
  have hIntBound : ∀ {f : 𝒮 → ℝ} {C : ℝ} (sₜ : 𝒮) (aₜ : 𝒜),
      (∀ y, ‖f y‖ ≤ C) → ‖∫ y, f y ∂(M.trans (sₜ, aₜ))‖ ≤ C := by
    intro f C sₜ aₜ hf
    simpa [probReal_univ] using
      norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, aₜ))
        (Filter.Eventually.of_forall hf)
  let T (κ : Θ) (sₜ : 𝒮) (aₜ : 𝒜) : ℝ :=
    ∫ y, M.V0 κ γ y ∂(M.trans (sₜ, aₜ))
  let Q (κ : Θ) (sₜ : 𝒮) (aₜ : 𝒜) : ℝ :=
    M.rkd sₜ aₜ + γ * T κ sₜ aₜ
  let backup (κ_π κ_bar : Θ) (sₜ : 𝒮) : ℝ :=
    ∫ u, M.π[κ_bar] sₜ u * Q κ_π sₜ u ∂ReferenceMeasure.measure
  have hπI : ∀ κ x, Integrable (M.π[κ] x) ReferenceMeasure.measure := by
    intro κ x
    apply Integrable.of_integral_ne_zero
    exact (hStoch.integral_eq_one κ x).symm ▸ one_ne_zero
  have hπu : ∀ κ x, Measurable (M.π[κ] x) :=
    fun κ x => (hπm κ).comp measurable_prodMk_left
  have hT : ∀ κ x, Measurable (T κ x) :=
    fun κ x =>
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.transK)
        (f := fun z => M.V0 κ γ z.2)
        ((hV κ).stronglyMeasurable.comp_measurable measurable_snd)).measurable).comp
        measurable_prodMk_left
  have hQmeas : ∀ κ x, Measurable (Q κ x) := fun κ x =>
    ((MeasurableRkd (M := M)).comp measurable_prodMk_left).add
      (measurable_const.mul (hT κ x))
  have hmulI : ∀ {κ : Θ} {g : 𝒜 → ℝ} {C : ℝ} (sₜ : 𝒮),
      Measurable g →
        (∀ u, ‖g u‖ ≤ C) →
          Integrable (fun u => M.π[κ] sₜ u * g u)
            ReferenceMeasure.measure := by
    intro κ g C sₜ hg hgC
    apply ((hπI κ sₜ).mul_const _).mono'
    · exact ((hπu κ sₜ).mul hg).aestronglyMeasurable
    ·
      apply Filter.Eventually.of_forall
      intro u
      rw [norm_mul, Real.norm_eq_abs]
      calc
        |M.π[κ] sₜ u| * ‖g u‖
            = M.π[κ] sₜ u * ‖g u‖ := by
          congr 1
          exact abs_of_nonneg (hStoch.nonneg κ sₜ u)
        _ ≤ M.π[κ] sₜ u * C :=
          mul_le_mul_of_nonneg_left (hgC u) (hStoch.nonneg κ sₜ u)
  have hQI : ∀ κ_π κ_bar sₜ,
      Integrable (fun aₜ => M.π[κ_bar] sₜ aₜ * Q κ_π sₜ aₜ)
        ReferenceMeasure.measure := by
    intro κ_π κ_bar x
    apply hmulI (C := |M.R| + |γ| * ((1 - γ)⁻¹ * |M.R|)) x
      (hQmeas κ_π x)
    intro u
    have hR := NormRkd.le.Abs_R (M := M) x u
    have hVint := hIntBound (sₜ := x) (aₜ := u) (hBound κ_π)
    calc
      _ ≤ ‖M.rkd x u‖ + ‖γ * T κ_π x u‖ :=
        norm_add_le _ _
      _ = ‖M.rkd x u‖ + |γ| * ‖T κ_π x u‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ |M.R| + |γ| * ((1 - γ)⁻¹ * |M.R|) :=
        add_le_add (by simpa [Real.norm_eq_abs] using hR)
          (mul_le_mul_of_nonneg_left hVint (abs_nonneg _))
  have hE : ∀ κ_π κ_bar x,
      Expectation.ofRV (M.kernel κ_bar x) (id : 𝒜 → 𝒜) (Q κ_π x) = backup κ_π κ_bar x := by
    intro κ_π κ_bar x
    simp only [Expectation.ofRV, expectation_real, Measure.map_id]
    have hpdf : Measurable (M.pdf κ_bar x) :=
      (M.measurable_pdf κ_bar).comp
        (Measurable.prodMk measurable_const measurable_id)
    have hker : M.kernel κ_bar x =
        ReferenceMeasure.measure.withDensity (M.pdf κ_bar x) :=
      Eq_WithDensity_Pdf (M := M) κ_bar x
    rw [hker, integral_withDensity_eq_integral_toReal_smul hpdf
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Policy.pdf, smul_eq_mul]
    rw [show (ENNReal.ofReal (M.π[κ_bar] x u)).toReal =
        M.π[κ_bar] x u from
      ENNReal.toReal_ofReal (hStoch.nonneg κ_bar x u)]
  have hVQ : ∀ κ x, M.V0 κ γ x = backup κ κ x := by
    intro κ sₜ
    have hBell :=
      Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob (M := M) hπm hγ κ sₜ
    have hr : Integrable (fun aₜ => M.π[κ] sₜ aₜ * M.rkd sₜ aₜ)
        ReferenceMeasure.measure :=
      hmulI sₜ ((MeasurableRkd (M := M)).comp measurable_prodMk_left)
        fun u => NormRkd.le.Abs_R (M := M) sₜ u
    have hc : Integrable (fun aₜ => M.π[κ] sₜ aₜ * T κ sₜ aₜ)
        ReferenceMeasure.measure :=
      hmulI sₜ (hT κ sₜ) fun u => hIntBound sₜ u (hBound κ)
    have hsum :
      ∫ aₜ, M.π[κ] sₜ aₜ * M.rkd sₜ aₜ ∂ReferenceMeasure.measure +
          ∫ aₜ, γ * (M.π[κ] sₜ aₜ * T κ sₜ aₜ) ∂ReferenceMeasure.measure =
        ∫ aₜ, M.π[κ] sₜ aₜ * Q κ sₜ aₜ ∂ReferenceMeasure.measure := by
      rw [← integral_add hr (hc.const_mul γ)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      simp only [Q]
      ring
    rw [hBell, ← integral_const_mul, hsum]
  let Δ : 𝒮 → ℝ := fun x => M.V0 θ' γ x - M.V0 θ γ x
  let TΔ (sₜ : 𝒮) (aₜ : 𝒜) : ℝ := ∫ y, Δ y ∂(M.trans (sₜ, aₜ))
  have hΔm : Measurable Δ := (hV θ').sub (hV θ)
  have hΔb : ∀ y, ‖Δ y‖ ≤ 2 * ((1 - γ)⁻¹ * |M.R|) := by
    intro y
    apply (norm_sub_le _ _).trans
    have := add_le_add (hBound θ' y) (hBound θ y)
    simpa [two_mul] using this
  have hΔbb : BddBelow (Set.range Δ) := by
    refine ⟨-(2 * ((1 - γ)⁻¹ * |M.R|)), ?_⟩
    rintro _ ⟨y, rfl⟩
    apply (abs_le.mp _).1
    simpa [Real.norm_eq_abs] using hΔb y
  let infΔ : ℝ := ⨅ y, Δ y
  have hI : ∀ sₜ,
      ∫ aₜ, M.π[θ'] sₜ aₜ * TΔ sₜ aₜ ∂ReferenceMeasure.measure ≥
        infΔ := by
    intro sₜ
    have hinner : ∀ u, TΔ sₜ u ≥ infΔ := fun u => by
      have hInt : Integrable Δ (M.trans (sₜ, u)) :=
        Integrable.of_bound hΔm.aestronglyMeasurable _
          (Filter.Eventually.of_forall hΔb)
      calc
        _ ≥ ∫ y, infΔ ∂(M.trans (sₜ, u)) :=
          integral_mono (integrable_const _) hInt (fun y => ciInf_le hΔbb y)
        _ = infΔ := by
          simp
    have hTΔ : Measurable (TΔ sₜ) :=
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.transK)
        (f := fun z => Δ z.2)
        (hΔm.stronglyMeasurable.comp_measurable measurable_snd)).measurable).comp
        measurable_prodMk_left
    have hc : Integrable (fun aₜ => M.π[θ'] sₜ aₜ * TΔ sₜ aₜ)
        ReferenceMeasure.measure :=
      hmulI sₜ hTΔ fun u => hIntBound sₜ u hΔb
    have hconst : Integrable (fun aₜ => M.π[θ'] sₜ aₜ * infΔ)
        ReferenceMeasure.measure :=
      (hπI θ' sₜ).mul_const _
    calc
      _ ≥ ∫ aₜ, M.π[θ'] sₜ aₜ * infΔ ∂ReferenceMeasure.measure :=
        integral_mono hconst hc (fun u =>
          mul_le_mul_of_nonneg_left (hinner u) (hStoch.nonneg θ' sₜ u))
      _ = ∫ aₜ, infΔ * M.π[θ'] sₜ aₜ ∂ReferenceMeasure.measure :=
        integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
      _ = infΔ * ∫ aₜ, M.π[θ'] sₜ aₜ ∂ReferenceMeasure.measure :=
        integral_const_mul infΔ (M.π[θ'] sₜ)
      _ = infΔ := by
        rw [show ∫ aₜ, M.π[θ'] sₜ aₜ ∂ReferenceMeasure.measure = 1 from
          hStoch.integral_eq_one θ' sₜ, mul_one]
  have hleft : ∀ x, Δ x ≥ γ * infΔ := by
    intro sₜ
    let I : ℝ :=
      ∫ aₜ, M.π[θ'] sₜ aₜ * TΔ sₜ aₜ ∂ReferenceMeasure.measure
    have hsub :
      backup θ' θ' sₜ - backup θ θ' sₜ =
        ∫ aₜ, M.π[θ'] sₜ aₜ * (Q θ' sₜ aₜ - Q θ sₜ aₜ)
          ∂ReferenceMeasure.measure := by
      rw [← integral_sub (hQI θ' θ' sₜ) (hQI θ θ' sₜ)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      ring
    have hQΔ : ∀ u, Q θ' sₜ u - Q θ sₜ u = γ * TΔ sₜ u := by
      intro u
      have hIntV (κ : Θ) : Integrable (M.V0 κ γ) (M.trans (sₜ, u)) :=
        Integrable.of_bound (hV κ).aestronglyMeasurable _
          (Filter.Eventually.of_forall (hBound κ))
      calc
        _ = M.rkd sₜ u + γ * T θ' sₜ u - (M.rkd sₜ u + γ * T θ sₜ u) :=
          rfl
        _ = γ * T θ' sₜ u - γ * T θ sₜ u := by
          ring
        _ = γ * (T θ' sₜ u - T θ sₜ u) := by
          ring
        _ = γ * TΔ sₜ u := by
          simp only [T, TΔ, Δ]
          rw [← integral_sub (hIntV θ') (hIntV θ)]
    have hγI : backup θ' θ' sₜ - backup θ θ' sₜ = γ * I := by
      rw [hsub, ← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp
      rw [hQΔ u]
      ring
    have hsplit : Δ sₜ = γ * I + (backup θ θ' sₜ - backup θ θ sₜ) := by
      change M.V0 θ' γ sₜ - M.V0 θ γ sₜ = _
      rw [hVQ θ' sₜ, hVQ θ sₜ, sub_eq_iff_eq_add.mp hγI]
      ring
    have hpen : 𝔇 θ θ' sₜ ≤ backup θ θ' sₜ - backup θ θ sₜ := by
      have hx :
        Expectation.ofRV (M.kernel θ' sₜ) (id : 𝒜 → 𝒜) (Q θ sₜ) - 𝔇 θ θ' sₜ ≥
          Expectation.ofRV (M.kernel θ sₜ) (id : 𝒜 → 𝒜) (Q θ sₜ) - 𝔇 θ θ sₜ := by
        simpa [mirror, Expectation.asRV, Q, T] using hℳ sₜ
      rw [hE θ θ' sₜ, hE θ θ sₜ] at hx
      simp [hD0 sₜ, sub_zero] at hx
      exact le_sub_comm.mp hx
    calc
      _ = γ * I + (backup θ θ' sₜ - backup θ θ sₜ) :=
        hsplit
      _ ≥ γ * I + 𝔇 θ θ' sₜ :=
        (add_le_add (le_refl (γ * I)) hpen).ge
      _ ≥ γ * I :=
        (le_add_of_nonneg_right (hD sₜ)).ge
      _ ≥ γ * infΔ :=
        (mul_le_mul_of_nonneg_left (hI sₜ) hγ.1).ge
  have hinf : 0 ≤ infΔ := by
    apply (mul_nonneg_iff_of_pos_left (sub_pos.mpr hγ.2)).mp
    convert sub_nonneg.mpr (le_ciInf fun x => hleft x)
    ring
  have hVge : ∀ x, M.V0 θ' γ x ≥ M.V0 θ γ x := fun x =>
    sub_nonneg.mp (le_trans hinf (ciInf_le hΔbb x))
  refine And.intro hVge ?_
  have hInt (κ : Θ) : Integrable (M.V0 κ γ) (M.init : Measure _) :=
    Integrable.of_bound (hV κ).aestronglyMeasurable _
      (Filter.Eventually.of_forall (hBound κ))
  exact integral_mono (hInt θ) (hInt θ') hVge


-- created on 2023-04-20
-- updated on 2026-11-17