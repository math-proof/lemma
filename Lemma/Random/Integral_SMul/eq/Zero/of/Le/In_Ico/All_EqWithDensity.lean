import Lemma.Random.SubAddKfMul_KfKf.eq.Zero.of.In_Ico.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Theorem.Function
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.MEq_V0.of.In_Ico.All_Eq.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real Finset Filter Kernel
set_option maxHeartbeats 800000


private lemma int_hist_mul
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) (n k : ℕ)
  {G : (Π _ : Finset.Iic n, ℝ × 𝒮 × 𝒜) → ℝ}
  (hG : StronglyMeasurable G) {CG : ℝ} (hCG : ∀ h, ‖G h‖ ≤ CG)
  {g : ℝ × 𝒮 × 𝒜 → ℝ} (hg : StronglyMeasurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
  Integrable (fun ω => G (Preorder.frestrictLe n ω) * g (ω k)) (M θ) := by
  refine Integrable.of_bound (C := CG * C) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((hG.comp_measurable (Preorder.measurable_frestrictLe n)).mul
      (hg.comp_measurable (measurable_pi_apply k))).aestronglyMeasurable
  ·
    rw [norm_mul]
    exact mul_le_mul (hCG _) (hC _) (norm_nonneg _)
      ((norm_nonneg _).trans (hCG (Preorder.frestrictLe n ω)))


/--
For `t ≤ n`, `𝔼[δ[n+1] * ψ(s[t], a[t])] = 0` under the continuous-action path law
(Markov property along histories + the textbook Bellman equation for `M.V` / `V0`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (t n : ℕ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (h₂ : t ≤ n)
  (θ : Θ)
  (hVm : ∀ k, Measurable (M.V θ γ k))
  (ψ : 𝒮 → 𝒜 → ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
-- imply
  ∫ ω, (r (n + 1) ω + γ * M.V θ γ (n + 1 + 1) (s (n + 1 + 1) ω) - M.V θ γ (n + 1) (s (n + 1) ω)) *
    ψ (s t ω) (a t ω) ∂(M θ) = 0 := by
-- proof
  classical
  obtain ⟨Ms, hMs⟩ := hMs
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  let Gh : (Π _ : Finset.Iic n, ℝ × 𝒮 × 𝒜) → ℝ := fun h =>
    ψ (h ⟨t, mem_Iic.2 h₂⟩).2.1 (h ⟨t, mem_Iic.2 h₂⟩).2.2
  have hG : StronglyMeasurable Gh :=
    hψ.comp_measurable
      ((measurable_snd.fst.comp (measurable_pi_apply _)).prodMk
        (measurable_snd.snd.comp (measurable_pi_apply _)))
  have hCG : ∀ h, ‖Gh h‖ ≤ Ms := fun h => hMs _ _
  set BV : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBV0 : 0 ≤ BV :=
    mul_nonneg (inv_nonneg.2 (le_of_lt (sub_pos.2 h₀.2))) (abs_nonneg _)
  -- Bounded modifications of `M.V θ γ (n+1)` and `M.V θ γ (n+2)`, so the Kf bounds stay pointwise.
  let fV1 : ℝ × 𝒮 × 𝒜 → ℝ := fun w => clip (M.V θ γ (n + 1) w.2.1) (-BV) BV
  let fV2 : ℝ × 𝒮 × 𝒜 → ℝ := fun w => clip (M.V θ γ (n + 2) w.2.1) (-BV) BV
  have hfV1 : StronglyMeasurable fV1 :=
    (((((hVm (n + 1))).comp measurable_snd.fst).max
      measurable_const).min measurable_const).stronglyMeasurable
  have hfV2 : StronglyMeasurable fV2 :=
    (((((hVm (n + 2))).comp measurable_snd.fst).max
      measurable_const).min measurable_const).stronglyMeasurable
  have hCV1 : ∀ w, ‖fV1 w‖ ≤ BV := fun w => by
    have := NormClip.le.Abs_R (R := BV) (ρ := M.V θ γ (n + 1) w.2.1)
    simpa [fV1, Real.norm_eq_abs, abs_of_nonneg hBV0] using this
  have hCV2 : ∀ w, ‖fV2 w‖ ≤ BV := fun w => by
    have := NormClip.le.Abs_R (R := BV) (ρ := M.V θ γ (n + 2) w.2.1)
    simpa [fV2, Real.norm_eq_abs, abs_of_nonneg hBV0] using this
  have hclip : StronglyMeasurable fun (w : ℝ × 𝒮 × 𝒜) => clip w.1 (-M.env.R) M.env.R :=
    ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hCclip : ∀ (w : ℝ × 𝒮 × 𝒜), ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  have h1 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hclip hCclip θ 1 n hG hCG
  have h2 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV2 hCV2 θ 2 n hG hCG
  have h3 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV1 hCV1 θ 1 n hG hCG
  have i1 := int_hist_mul M θ n (n + 1) hG hCG hclip hCclip
  have i2 := int_hist_mul M θ n (n + 2) hG hCG hfV2 hCV2
  have i3 := int_hist_mul M θ n (n + 1) hG hCG hfV1 hCV1
  have k1 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hclip hCclip θ 1
  have k2 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV2 hCV2 θ 2
  have k3 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV1 hCV1 θ 1
  have j1 := int_hist_mul M θ n n hG hCG k1.1 k1.2
  have j2 := int_hist_mul M θ n n hG hCG k2.1 k2.2
  have j3 := int_hist_mul M θ n n hG hCG k3.1 k3.2
  -- Pathwise a.e. bounds, so `V` agrees with its clip along the trajectory.
  have hrm : ∀ k, Measurable (r k) := fun k => Random.Measurable.of.All_Eq.fst h₁ k
  have hsm : ∀ k, Measurable (s k) := fun k => Random.Measurable.of.All_Eq.snd.fst h₁ k
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : ∀ k, Measurable
      (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k =>
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  have hr_bd : ∀ᵐ ω ∂(M θ), ∀ j, |r j ω| ≤ |M.env.R| := by
    have hcl : ∀ j,
        r j =ᵐ[M θ] fun ω => clip (ω j).1 (-M.env.R) M.env.R := fun j =>
      MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ j
    have hcl' : ∀ᵐ ω ∂(M θ), ∀ j,
        r j ω = clip (ω j).1 (-M.env.R) M.env.R :=
      (ae_all_iff (ι := ℕ)).mpr hcl
    filter_upwards [hcl'] with ω hω j
    rw [hω j, ← Real.norm_eq_abs]
    exact NormClip.le.Abs_R (R := M.env.R) (ρ := (ω j).1)
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ k,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BV := by
    have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    filter_upwards [hr_bd] with ω hω k
    refine tsum_of_norm_bounded hgeo fun j => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
    have hslice : (fun i => r i ω)[k:] j = r (k + j) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (k + j)) (pow_nonneg h₀.1 j)
  have hret : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] := fun k =>
    (hfGret k).comp hpR
  have hGi : ∀ k,
      Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M θ) :=
    fun k =>
      Integrable.of_bound (hret k).aestronglyMeasurable BV
        (by filter_upwards [hret_bd] with ω hω; exact hω k)
  have hV_ae : ∀ k,
      (fun ω => M.V θ γ k (s k ω)) =ᵐ[M θ]
        Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k => by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω i => r i ω) (y := s k)
        (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:])
        hpR.aemeasurable (hsm k) (hfGret k).stronglyMeasurable (hGi k)
    filter_upwards [hcomp] with ω hω
    exact hω
  have hVbd : ∀ᵐ ω ∂(M θ), ∀ k, |M.V θ γ k (s k ω)| ≤ BV := by
    have hcond : ∀ k, ∀ᵐ ω ∂(M θ),
        |Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) ω| ≤ BV := fun k => by
      have hbd :=
        ae_bdd_norm_condExp_of_ae_bdd_norm
          (f := fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun i => r i ω)[k:])
          (m := MeasurableSpace.comap (s k) inferInstance)
          (by filter_upwards [hret_bd] with ω hω; exact hω k)
      filter_upwards [hbd] with ω h
      simpa [Expectation.condSigma, Real.norm_eq_abs] using h
    have hVeq := (ae_all_iff (ι := ℕ)).mpr hV_ae
    have hVnorm := (ae_all_iff (ι := ℕ)).mpr hcond
    filter_upwards [hVeq, hVnorm] with ω heq hnorm k
    rw [heq k]
    exact hnorm k
  have hae : ∀ᵐ ω ∂(M θ),
      (r (n + 1) ω + γ * M.V θ γ (n + 1 + 1) (s (n + 1 + 1) ω) - M.V θ γ (n + 1) (s (n + 1) ω)) *
        ψ (s t ω) (a t ω) =
        Gh (Preorder.frestrictLe n ω) * clip (ω (n + 1)).1 (-M.env.R) M.env.R +
          γ * (Gh (Preorder.frestrictLe n ω) * fV2 (ω (n + 2))) -
          Gh (Preorder.frestrictLe n ω) * fV1 (ω (n + 1)) := by
    filter_upwards [MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ (n + 1),
      hVbd] with ω hω hVb
    have hGω : Gh (Preorder.frestrictLe n ω) = ψ (s t ω) (a t ω) := rfl
    have hclipV : ∀ (x : ℝ), |x| ≤ BV → clip x (-BV) BV = x := fun x hx => by
      -- clip x lo hi = min (max x lo) hi
      have hlo : -BV ≤ x := (abs_le.mp hx).1
      have hhi : x ≤ BV := (abs_le.mp hx).2
      rw [clip, max_eq_left hlo, min_eq_left hhi]
    have h1' : fV1 (ω (n + 1)) = M.V θ γ (n + 1) (s (n + 1) ω) := by
      simp only [fV1, s]
      exact hclipV _ (hVb (n + 1))
    have h2' : fV2 (ω (n + 2)) = M.V θ γ (n + 2) (s (n + 2) ω) := by
      simp only [fV2, s]
      exact hclipV _ (hVb (n + 2))
    rw [hGω, hω, h1', h2', mul_comm (ψ (s t ω) (a t ω))]
    ring
  have i23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * fV2 (ω (n + 2)))) (M θ) :=
    i2.const_mul γ
  have j23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV2 2 (ω n))) (M θ) :=
    j2.const_mul γ
  have ia : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) *
      clip (ω (n + 1)).1 (-M.env.R) M.env.R +
        γ * (Gh (Preorder.frestrictLe n ω) * fV2 (ω (n + 2)))) (M θ) := i1.add i23
  have ja : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) *
      M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
        γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV2 2 (ω n))) (M θ) := j1.add j23
  rw [integral_congr_ae hae, integral_sub ia i3, integral_add i1 i23, integral_const_mul,
    h1, h2, h3]
  have e := integral_sub ja j3
  rw [integral_add j1 j23, integral_const_mul] at e
  rw [← e]

  -- Identify the free V with the kernel value V0 a.e., then apply the
  -- existing V0 Bellman identity for Kf.
  have hVV0 : ∀ k, (fun ω => M.V θ γ k (s k ω)) =ᵐ[M θ]
      (fun ω => M.V0 θ γ (s k ω)) := fun k =>
    (hV_ae k).trans (MEq_V0.of.In_Ico.All_Eq.All_EqWithDensity (M := M) h₀ h₁ hπ θ k).symm
  let fV : ℝ × 𝒮 × 𝒜 → ℝ := fun w => M.V0 θ γ w.2.1
  have hfV : StronglyMeasurable fV :=
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
      measurable_snd.fst).stronglyMeasurable
  have hCV : ∀ w, ‖fV w‖ ≤ BV := fun w =>
    NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ w.2.1
  have h2V := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 2 n hG hCG
  have h3V := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 1 n hG hCG
  have k2V := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 2
  have k3V := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 1
  have j2V := int_hist_mul M θ n n hG hCG k2V.1 k2V.2
  have j3V := int_hist_mul M θ n n hG hCG k3V.1 k3V.2
  have hclipV : ∀ (x : ℝ), |x| ≤ BV → clip x (-BV) BV = x := fun x hx => by
    have hlo : -BV ≤ x := (abs_le.mp hx).1
    have hhi : x ≤ BV := (abs_le.mp hx).2
    rw [clip, max_eq_left hlo, min_eq_left hhi]
  have haeV1 : ∀ᵐ ω ∂(M θ), fV1 (ω (n + 1)) = fV (ω (n + 1)) := by
    filter_upwards [hVbd, hVV0 (n + 1)] with ω hVb hV0
    simp only [fV1, fV]
    rw [hclipV _ (hVb (n + 1)), hV0]
  have haeV2 : ∀ᵐ ω ∂(M θ), fV2 (ω (n + 2)) = fV (ω (n + 2)) := by
    filter_upwards [hVbd, hVV0 (n + 2)] with ω hVb hV0
    simp only [fV2, fV]
    rw [hclipV _ (hVb (n + 2)), hV0]
  have eKf1 :
      ∫ ω, Gh (Preorder.frestrictLe n ω) * M.Kf θ fV1 1 (ω n) ∂(M θ) =
        ∫ ω, Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 1 (ω n) ∂(M θ) := by
    have hL := h3
    have hR := h3V
    have hmid :
        ∫ ω, Gh (Preorder.frestrictLe n ω) * fV1 (ω (n + 1)) ∂(M θ) =
          ∫ ω, Gh (Preorder.frestrictLe n ω) * fV (ω (n + 1)) ∂(M θ) :=
      integral_congr_ae (by
        filter_upwards [haeV1] with ω hω
        rw [hω])
    exact hL.symm.trans (hmid.trans hR)
  have eKf2 :
      ∫ ω, Gh (Preorder.frestrictLe n ω) * M.Kf θ fV2 2 (ω n) ∂(M θ) =
        ∫ ω, Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n) ∂(M θ) := by
    have hL := h2
    have hR := h2V
    have hmid :
        ∫ ω, Gh (Preorder.frestrictLe n ω) * fV2 (ω (n + 2)) ∂(M θ) =
          ∫ ω, Gh (Preorder.frestrictLe n ω) * fV (ω (n + 2)) ∂(M θ) :=
      integral_congr_ae (by
        filter_upwards [haeV2] with ω hω
        rw [hω])
    exact hL.symm.trans (hmid.trans hR)
  have j23V : Integrable
      (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n))) (M θ) :=
    j2V.const_mul γ
  have jaV : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) *
      M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
        γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n))) (M θ) :=
    j1.add j23V
  -- rewrite the fV1/fV2 kernel integral to the V0 kernel integral
  have hrewrite :
      ∫ ω, Gh (Preorder.frestrictLe n ω) *
            M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
          γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV2 2 (ω n)) -
          Gh (Preorder.frestrictLe n ω) * M.Kf θ fV1 1 (ω n) ∂(M θ) =
        ∫ ω, Gh (Preorder.frestrictLe n ω) *
            M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
          γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n)) -
          Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 1 (ω n) ∂(M θ) := by
    have hs12 :
        ∫ ω, Gh (Preorder.frestrictLe n ω) *
              M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
            γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV2 2 (ω n)) ∂(M θ) =
          ∫ ω, Gh (Preorder.frestrictLe n ω) *
              M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
            γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n)) ∂(M θ) := by
      rw [integral_add j1 j23, integral_add j1 j23V, integral_const_mul, integral_const_mul,
        eKf2]
    exact (integral_sub ja j3).trans
      ((congrArg₂ (fun x y => x - y) hs12 eKf1).trans (integral_sub jaV j3V).symm)
  rw [hrewrite]
  have hz : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
      Gh (Preorder.frestrictLe n ω) *
          M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
        γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n)) -
        Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 1 (ω n) = 0 := fun ω => by
    have := SubAddKfMul_KfKf.eq.Zero.of.In_Ico.All_EqWithDensity (M := M) h₀ hπ θ (ω n)
    calc
      _ = Gh (Preorder.frestrictLe n ω) *
          (M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
            γ * M.Kf θ fV 2 (ω n) - M.Kf θ fV 1 (ω n)) := by
        ring
      _ = 0 := by rw [this, mul_zero]
  simp_rw [hz]
  simp


-- created on 2026-10-20
-- updated on 2026-11-12
