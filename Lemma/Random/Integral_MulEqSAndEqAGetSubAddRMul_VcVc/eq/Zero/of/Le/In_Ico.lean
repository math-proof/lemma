import sympy.stats.policy_trajectory.advantage
import sympy.Basic
import Lemma.Random.SubAddKfMul_KfKf.eq.Zero.of.In_Ico
import Lemma.Random.AeR.eq.Rc
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm.le.Sum_Norm
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real Finset Filter


private lemma int_hist_mul [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] (M : Model Θ S A) (θ : Θ) (n k : ℕ) {G : (Π _ : Iic n, ℝ × S × A) → ℝ} (hG : StronglyMeasurable G) {CG : ℝ} (hCG : ∀ h, ‖G h‖ ≤ CG) {g : ℝ × S × A → ℝ} (hg : StronglyMeasurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
    Integrable (fun ω => G (Preorder.frestrictLe n ω) * g (ω k)) (M θ) := by
  refine Integrable.of_bound (C := CG * C) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((hG.comp_measurable (Preorder.measurable_frestrictLe n)).mul
      (hg.comp_measurable (measurable_pi_apply k))).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul (hCG _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hCG (Preorder.frestrictLe n ω)))

/--
For `t ≤ n`, `𝔼[1{s[t] = x ∧ a[t] = u} * δ[n+1]] = 0` (Markov property along histories + Bellman equation).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (t n : ℕ)
  (h₁ : t ≤ n)
  (x : S)
  (u : A) :
-- imply
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
    (r (n + 1) ω + γ * M.Vc θ γ (s (n + 1 + 1) ω) - M.Vc θ γ (s (n + 1) ω)) ∂(M θ) = 0 := by
-- proof
  let Gh : (Π _ : Iic n, ℝ × S × A) → ℝ := fun h =>
    if (h ⟨t, mem_Iic.2 h₁⟩).2.1 = x ∧ (h ⟨t, mem_Iic.2 h₁⟩).2.2 = u then (1:ℝ) else 0
  have hG : StronglyMeasurable Gh :=
    (StronglyMeasurable.discrete (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0)).comp_measurable
      ((measurable_snd.fst.comp (measurable_pi_apply _)).prodMk
        (measurable_snd.snd.comp (measurable_pi_apply _)))
  have hCG : ∀ h, ‖Gh h‖ ≤ 1 := fun h => by dsimp only [Gh]; split_ifs <;> simp
  have hGω : ∀ ω : ℕ → ℝ × S × A, Gh (Preorder.frestrictLe n ω) =
      (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) := fun ω => rfl
  let f : ℝ × S × A → ℝ := fun w => M.Vc θ γ w.2.1
  have hf : StronglyMeasurable f := (StronglyMeasurable.discrete (M.Vc θ γ)).comp_measurable measurable_snd.fst
  have hC : ∀ w, ‖f w‖ ≤ ∑ y', ‖M.Vc θ γ y'‖ := fun w => Norm.le.Sum_Norm (M.Vc θ γ) w.2.1
  have h1 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ 1 n hG hCG
  have h2 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 2 n hG hCG
  have h3 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 1 n hG hCG
  have i1 := int_hist_mul M θ n (n + 1) hG hCG (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M))
  have i2 := int_hist_mul M θ n (n + 2) hG hCG hf hC
  have i3 := int_hist_mul M θ n (n + 1) hG hCG hf hC
  have k1 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ 1
  have k2 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 2
  have k3 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 1
  have j1 := int_hist_mul M θ n n hG hCG k1.1 k1.2
  have j2 := int_hist_mul M θ n n hG hCG k2.1 k2.2
  have j3 := int_hist_mul M θ n n hG hCG k3.1 k3.2
  have hae : ∀ᵐ ω ∂(M θ),
      (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (r (n + 1) ω + γ * M.Vc θ γ (s (n + 1 + 1) ω) - M.Vc θ γ (s (n + 1) ω)) =
      Gh (Preorder.frestrictLe n ω) * M.rc (ω (n + 1)) +
        γ * (Gh (Preorder.frestrictLe n ω) * f (ω (n + 2))) -
        Gh (Preorder.frestrictLe n ω) * f (ω (n + 1)) := by
    filter_upwards [AeR.eq.Rc (M := M) θ (n + 1)] with ω hω
    rw [hGω, hω]
    show _ * (M.rc (ω (n + 1)) + γ * M.Vc θ γ (ω (n + 2)).2.1 - M.Vc θ γ (ω (n + 1)).2.1) = _
    ring
  have hz : ∀ ω : ℕ → ℝ × S × A, Gh (Preorder.frestrictLe n ω) * M.Kf θ M.rc 1 (ω n) +
      γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ f 2 (ω n)) -
      Gh (Preorder.frestrictLe n ω) * M.Kf θ f 1 (ω n) = 0 := fun ω => by
    have := SubAddKfMul_KfKf.eq.Zero.of.In_Ico (M := M) θ h₀ (ω n)
    calc _ = Gh (Preorder.frestrictLe n ω) *
        (M.Kf θ M.rc 1 (ω n) + γ * M.Kf θ f 2 (ω n) - M.Kf θ f 1 (ω n)) := by ring
      _ = 0 := by rw [this, mul_zero]
  have i23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * f (ω (n + 2)))) (M θ) :=
    i2.const_mul γ
  have j23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ f 2 (ω n))) (M θ) :=
    j2.const_mul γ
  have ia : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) * M.rc (ω (n + 1)) +
      γ * (Gh (Preorder.frestrictLe n ω) * f (ω (n + 2)))) (M θ) := i1.add i23
  have ja : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) * M.Kf θ M.rc 1 (ω n) +
      γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ f 2 (ω n))) (M θ) := j1.add j23
  rw [integral_congr_ae hae, integral_sub ia i3, integral_add i1 i23, integral_const_mul,
    h1, h2, h3]
  have e := integral_sub ja j3
  rw [integral_add j1 j23, integral_const_mul] at e
  rw [← e]
  simp_rw [hz]
  simp


-- created on 2026-10-06
