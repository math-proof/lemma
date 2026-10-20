import Lemma.Random.SubAddKfMul_KfKf.eq.Zero.of.In_Ico.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real Finset Filter
set_option maxHeartbeats 800000


private lemma int_hist_mul
  [MeasurableSpace S] [ReferenceMeasure A]
  (M : DensityModel Θ S A) (θ : Θ) (n k : ℕ)
  {G : (Π _ : Finset.Iic n, ℝ × S × A) → ℝ}
  (hG : StronglyMeasurable G) {CG : ℝ} (hCG : ∀ h, ‖G h‖ ≤ CG)
  {g : ℝ × S × A → ℝ} (hg : StronglyMeasurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
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
(Markov property along histories + Bellman equation).
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (t n : ℕ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A ↦ M.policy.prob θ z.1 z.2))
  (h₂ : t ≤ n)
  (θ : Θ)
  (ψ : S → A → ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
-- imply
  ∫ ω, (r (n + 1) ω + γ * M.Vkd θ γ (s (n + 1 + 1) ω) - M.Vkd θ γ (s (n + 1) ω)) *
    ψ (s t ω) (a t ω) ∂(M θ) = 0 := by
-- proof
  classical
  obtain ⟨Ms, hMs⟩ := hMs
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let Gh : (Π _ : Finset.Iic n, ℝ × S × A) → ℝ := fun h =>
    ψ (h ⟨t, mem_Iic.2 h₂⟩).2.1 (h ⟨t, mem_Iic.2 h₂⟩).2.2
  have hG : StronglyMeasurable Gh :=
    hψ.comp_measurable
      ((measurable_snd.fst.comp (measurable_pi_apply _)).prodMk
        (measurable_snd.snd.comp (measurable_pi_apply _)))
  have hCG : ∀ h, ‖Gh h‖ ≤ Ms := fun h => hMs _ _
  let fV : ℝ × S × A → ℝ := fun w => M.Vkd θ γ w.2.1
  have hfV : StronglyMeasurable fV :=
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp measurable_snd.fst).stronglyMeasurable
  have hCV : ∀ w, ‖fV w‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    fun w => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ w.2.1
  have hclip : StronglyMeasurable fun (w : ℝ × S × A) => clip w.1 (-M.env.R) M.env.R :=
    ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hCclip : ∀ (w : ℝ × S × A), ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  have h1 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hclip hCclip θ 1 n hG hCG
  have h2 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 2 n hG hCG
  have h3 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 1 n hG hCG
  have i1 := int_hist_mul M θ n (n + 1) hG hCG hclip hCclip
  have i2 := int_hist_mul M θ n (n + 2) hG hCG hfV hCV
  have i3 := int_hist_mul M θ n (n + 1) hG hCG hfV hCV
  have k1 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hclip hCclip θ 1
  have k2 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 2
  have k3 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 1
  have j1 := int_hist_mul M θ n n hG hCG k1.1 k1.2
  have j2 := int_hist_mul M θ n n hG hCG k2.1 k2.2
  have j3 := int_hist_mul M θ n n hG hCG k3.1 k3.2
  have hae : ∀ᵐ ω ∂(M θ),
      (r (n + 1) ω + γ * M.Vkd θ γ (s (n + 1 + 1) ω) - M.Vkd θ γ (s (n + 1) ω)) *
        ψ (s t ω) (a t ω) =
        Gh (Preorder.frestrictLe n ω) * clip (ω (n + 1)).1 (-M.env.R) M.env.R +
          γ * (Gh (Preorder.frestrictLe n ω) * fV (ω (n + 2))) -
          Gh (Preorder.frestrictLe n ω) * fV (ω (n + 1)) := by
    filter_upwards [MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ (n + 1)] with ω hω
    have hGω : Gh (Preorder.frestrictLe n ω) = ψ (s t ω) (a t ω) := rfl
    rw [hGω, hω, mul_comm (ψ (s t ω) (a t ω))]
    ring
  have hz : ∀ ω : ℕ → ℝ × S × A,
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
  have i23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * fV (ω (n + 2)))) (M θ) :=
    i2.const_mul γ
  have j23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n))) (M θ) :=
    j2.const_mul γ
  have ia : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) *
      clip (ω (n + 1)).1 (-M.env.R) M.env.R +
        γ * (Gh (Preorder.frestrictLe n ω) * fV (ω (n + 2)))) (M θ) := i1.add i23
  have ja : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) *
      M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
        γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n))) (M θ) := j1.add j23
  rw [integral_congr_ae hae, integral_sub ia i3, integral_add i1 i23, integral_const_mul,
    h1, h2, h3]
  have e := integral_sub ja j3
  rw [integral_add j1 j23, integral_const_mul] at e
  rw [← e]
  simp_rw [hz]
  simp


-- created on 2026-10-20
