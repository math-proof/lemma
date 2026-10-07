import sympy.stats.policy_trajectory.gradient
import Lemma.Random.MEqCondExp_Integral.of.Integrable.Measurable
import Lemma.Random.AeNe_0
import sympy.core.power
import sympy.vector.Basic
import Lemma.Random.Integrable_G.of.In_Ico
import Lemma.Random.AeR.eq.Rc
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral.eq.MulRealIntegral_MulIndicator1.of.MeasurableSet
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEq12.eq.MulEqIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEq12AndEq22.eq.MulMulRealProb
import Lemma.Random.Integral_MulEqSAndEqA.eq.MulMulRealProbSum_MulT
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable.discrete
import Lemma.Real.StronglyMeasurable_Eq12
import Lemma.Real.StronglyMeasurable_Eq12AndEq22
open MeasureTheory ProbabilityTheory PolicyGradient Random


/--
Markov property of the trajectory model `M θ`: given `(s[t], a[t], s[t+1])` the conditional expectation
of the future discounted return `γ ** Stack[k](k) @ r[t+1:]` only depends on `s[t+1]`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1) :
-- imply
  (M θ)[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t + 1:]) | MeasurableSpace.comap (fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) inferInstance] =ᵐ[M θ]
    (M θ)[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t + 1:]) | MeasurableSpace.comap (s (t + 1)) inferInstance] := by
-- proof
  classical
  have hX : Measurable (fun ω ↦ ((s (S := S) (A := A) t ω, a (S := S) (A := A) t ω), s (S := S) (A := A) (t + 1) ω)) :=
    ((Random.Measurable_S t).prodMk (Random.Measurable_A t)).prodMk (Random.Measurable_S (t + 1))
  have hF : Integrable (G (S := S) (A := A) γ (t + 1)) (M θ) := Integrable_G.of.In_Ico (M := M) θ h₀ (t + 1)
  have hKf := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ
  -- the kernel step: `𝔼[1{s[t+1] = y} * Kf(ω[t+1]) | ω[t] = w] = T(w, y) * W(y)`
  have hstep : ∀ (k : ℕ) (y : S) (w : ℝ × S × A),
      ∫ z, (if z.2.1 = y then (1 : ℝ) else 0) * M.Kf θ M.rc k z ∂(M.K θ w) = M.T w.2.1 w.2.2 y * M.W θ M.rc k y := by
    intro k y w
    have := M.env.trans_markov
    have hK : M.K θ w = M.stageK θ ∘ₘ M.env.trans (w.2.1, w.2.2) := by
      rw [Model.K, Kernel.comp_apply, Kernel.comap_apply]
    rw [hK, Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable (f := fun z : ℝ × S × A ↦ (if z.2.1 = y then (1 : ℝ) else 0) * M.Kf θ M.rc k z)
      (((Real.StronglyMeasurable.discrete (fun x : S ↦ if x = y then (1 : ℝ) else 0)).comp_measurable
        measurable_snd.fst).mul (hKf k).1) (Real.LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × S × A ↦ z.2.1 = y)) (hKf k).2),
      integral_fintype Integrable.of_finite]
    simp_rw [Integral_MulEq12.eq.MulEqIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (hKf k).1 (hKf k).2 θ y]
    rw [Finset.sum_eq_single y (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp only [if_true, one_mul, smul_eq_mul]
    rfl
  -- joint expectation of the reward on the atom `(s[t], a[t], s[t+1]) = (x, u, y)`
  have hE : ∀ (k : ℕ) (x : S) (u : A) (y : S),
      ∫ ω, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1 : ℝ) else 0) * (if (ω (t + 1)).2.1 = y then (1 : ℝ) else 0) *
        r (t + 1 + k) ω ∂(M θ) =
      (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * (M.T x u y * M.W θ M.rc k y) := by
    intro k x u y
    have hGt : StronglyMeasurable (fun h : (Π _ : Finset.Iic t, ℝ × S × A) ↦
        if (h ⟨t, Finset.mem_Iic.2 le_rfl⟩).2.1 = x ∧ (h ⟨t, Finset.mem_Iic.2 le_rfl⟩).2.2 = u then (1 : ℝ) else 0) :=
      (Real.StronglyMeasurable_Eq12AndEq22 x u).comp_measurable (measurable_pi_apply _)
    have hGh : StronglyMeasurable (fun h : (Π _ : Finset.Iic (t + 1), ℝ × S × A) ↦
        (if (h ⟨t, Finset.mem_Iic.2 (Nat.le_succ t)⟩).2.1 = x ∧ (h ⟨t, Finset.mem_Iic.2 (Nat.le_succ t)⟩).2.2 = u then (1 : ℝ) else 0) *
          (if (h ⟨t + 1, Finset.mem_Iic.2 le_rfl⟩).2.1 = y then (1 : ℝ) else 0)) :=
      ((Real.StronglyMeasurable_Eq12AndEq22 x u).comp_measurable (measurable_pi_apply _)).mul
        ((Real.StronglyMeasurable_Eq12 (A := A) y).comp_measurable (measurable_pi_apply _))
    have hg : StronglyMeasurable (fun z : ℝ × S × A ↦ (if z.2.1 = y then (1 : ℝ) else 0) * M.Kf θ M.rc k z) :=
      (Real.StronglyMeasurable_Eq12 (A := A) y).mul (hKf k).1
    calc _ = ∫ ω, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1 : ℝ) else 0) * (if (ω (t + 1)).2.1 = y then (1 : ℝ) else 0) *
          M.rc (ω (t + 1 + k)) ∂(M θ) :=
        integral_congr_ae ((AeR.eq.Rc (M := M) θ (t + 1 + k)).mono fun ω h ↦ by dsimp only; rw [h])
      _ = ∫ ω, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1 : ℝ) else 0) * (if (ω (t + 1)).2.1 = y then (1 : ℝ) else 0) *
          M.Kf θ M.rc k (ω (t + 1)) ∂(M θ) :=
        All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ k (t + 1) hGh (CG := 1)
          (fun h ↦ by rw [norm_mul]; exact mul_le_one₀ (Real.Norm_1.le.One _) (norm_nonneg _) (Real.Norm_1.le.One _))
      _ = ∫ ω, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1 : ℝ) else 0) *
          ((if (ω (t + 1)).2.1 = y then (1 : ℝ) else 0) * M.Kf θ M.rc k (ω (t + 1))) ∂(M θ) := by
        simp_rw [mul_assoc]
      _ = ∫ ω, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1 : ℝ) else 0) *
          ∫ z, (if z.2.1 = y then (1 : ℝ) else 0) * M.Kf θ M.rc k z ∂(M.K θ (ω t)) ∂(M θ) :=
        Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) (n := t) (CG := 1) hGt (fun h ↦ Real.Norm_1.le.One _) hg (Real.LeNorm_Mul1.of.All_LeNorm (hKf k).2) θ
      _ = ∫ ω, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1 : ℝ) else 0) *
          (fun x' u' ↦ M.T x' u' y * M.W θ M.rc k y) (ω t).2.1 (ω t).2.2 ∂(M θ) := by
        simp_rw [hstep]
      _ = _ := Integral_MulEq12AndEq22.eq.MulMulRealProb (M := M) θ t x u (fun x' u' ↦ M.T x' u' y * M.W θ M.rc k y)
  -- the conditional expected return on a reachable atom is `V(s[t+1] = y)`
  have hatom : ∀ (x : S) (u : A) (y : S),
      M θ ((fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) ⁻¹' {((x, u), y)}) ≠ 0 →
      ∫ ω, G γ (t + 1) ω ∂(M θ)[|(fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) ⁻¹' {((x, u), y)}] =
        ∫ ω, G γ (t + 1) ω ∂(M θ)[|s (t + 1) ⁻¹' {y}] := by
    intro x u y hB
    set B := (fun ω ↦ ((s (S := S) (A := A) t ω, a (S := S) (A := A) t ω), s (S := S) (A := A) (t + 1) ω)) ⁻¹' {((x, u), y)}
    have hBm : MeasurableSet B := hX (measurableSet_singleton _)
    have hind : ∀ ω, B.indicator 1 ω =
        (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1 : ℝ) else 0) * (if (ω (t + 1)).2.1 = y then (1 : ℝ) else 0) := by
      intro ω
      by_cases h₁ : (ω t).2.1 = x <;> by_cases h₂ : (ω t).2.2 = u <;> by_cases h₃ : (ω (t + 1)).2.1 = y <;>
        simp [B, s, a, h₁, h₂, h₃, Prod.ext_iff]
    have hPB : (M θ).real B = (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * M.T x u y := by
      rw [← integral_indicator_one hBm]
      have h := Integral_MulEqSAndEqA.eq.MulMulRealProbSum_MulT (M := M) θ t x u (fun y' ↦ if y' = y then (1 : ℝ) else 0)
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      rw [← h]
      congr 1
      funext ω
      rw [hind]
      by_cases h₁ : (ω t).2.1 = x <;> by_cases h₂ : (ω t).2.2 = u <;> by_cases h₃ : (ω (t + 1)).2.1 = y <;>
        simp [s, a, h₁, h₂, h₃]
    have hc : (M θ).real B ≠ 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).not.2 hB
    have hy : (M θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 := fun h ↦ hc (le_antisymm
      (h ▸ measureReal_mono (fun ω hω ↦ by simp_all [B]) (measure_ne_top _ _)) measureReal_nonneg)
    rw [Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ θ B (t + 1), ← Model.V_eq_integral, V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) θ (t + 1) y h₀ hy]
    congr 1
    funext k
    rw [Integral.eq.MulRealIntegral_MulIndicator1.of.MeasurableSet (M := M) hBm θ]
    simp_rw [hind]
    rw [hE k x u y, show (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * (M.T x u y * M.W θ M.rc k y) =
      (M θ).real B * M.W θ M.rc k y by rw [hPB]; ring, inv_mul_cancel_left₀ hc]
  refine (MEqCondExp_Integral.of.Integrable.Measurable hX hF).trans
    (Filter.EventuallyEq.trans ?_ (MEqCondExp_Integral.of.Integrable.Measurable (Random.Measurable_S (t + 1)) hF).symm)
  filter_upwards [Random.AeNe_0 (π := M θ) (X := fun ω ↦ ((s (S := S) (A := A) t ω, a (S := S) (A := A) t ω), s (S := S) (A := A) (t + 1) ω))] with ω hω
  exact hatom _ _ _ hω


-- created on 2026-10-06
