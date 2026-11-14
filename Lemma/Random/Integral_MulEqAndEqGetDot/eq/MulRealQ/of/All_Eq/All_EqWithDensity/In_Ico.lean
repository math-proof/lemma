import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Theorem.Probability.JointRv.AsRV
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * G[t]] = ℙ(s[t] = x, a[t] = u) * Q θ γ t x u`.
Continuous-action counterpart of
`Random.Integral_MulEqAndEqGetDot.eq.MulMulRealProbQ.of.All_Eq.In_Ico`:
the finite-action factorization `ℙ(s[t] = x) * π_θ(u | x)` is replaced by the
joint atom mass `ℙ(s[t] = x ∧ a[t] = u)`, which agrees with it when the
reference measure is counting measure.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  [DecidableEq 𝒮] [DecidableEq 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) * M.Q θ γ t x u := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set B : Set (ℕ → ℝ × 𝒮 × 𝒜) := s t ⁻¹' {x} ∩ a t ⁻¹' {u}
  have hX : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s t ω, a t ω)) :=
    (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
      (Random.Measurable.of.All_Eq.snd.snd h₁ t)
  have hpre : (fun ω => (s t ω, a t ω)) ⁻¹' {(x, u)} = B := by
    ext ω
    simp [B, s, a, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.ext_iff]
  have hBm : MeasurableSet B := by
    rw [← hpre]
    exact hX (measurableSet_singleton _)
  have hpR : Measurable (fun ω k ↦ r k ω) :=
    Measurable.of_eval fun k => measurable_fst.comp (measurable_pi_apply k)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) := by
    unfold Dot.dot Function.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  have hG : Measurable G := hfG.comp hpR
  have hι :
      (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * G ω) =
        B.indicator G := by
    funext ω
    by_cases h : s t ω = x ∧ a t ω = u <;>
      simp [h, B, s, a, G, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_inter_iff]
  have hι1 :
      (fun ω => B.indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) ω * G ω) =
        B.indicator G := by
    funext ω
    by_cases hω : ω ∈ B <;> simp [hω, Set.indicator]
  have hbound : ∀ᵐ ω ∂(M θ),
      ‖G ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ] with ω h
    have hb : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k)
    have hGω : G ω = ∑' k, γ ^ k * r (t + k) ω := by
      unfold G Dot.dot Function.getSliceFrom
      rfl
    rw [hGω]
    exact tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) hb
  have hInt : Integrable G (M θ) :=
    Integrable.of_bound hG.aestronglyMeasurable _ hbound
  rw [hι]
  if hB : (M θ) B = 0 then
    have hreal : (M θ).real B = 0 := by
      simp [Measure.real, hB]
    rw [integral_indicator hBm, setIntegral_measure_zero _ hB, hreal, zero_mul]
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    have hQA : (M θ).real B ≠ 0 := by
      intro hz
      exact hB ((ENNReal.toReal_eq_zero_iff _).1 hz |>.resolve_right
        (measure_ne_top (M θ) B))
    have hmap : (M θ).map (fun ω => (s t ω, a t ω)) {(x, u)} ≠ 0 := by
      rw [Measure.map_apply hX (measurableSet_singleton _), hpre]
      exact hB
    have hQ : M.Q θ γ t x u = ∫ ω, G ω ∂(M θ)[|B] := by
      unfold DensityModel.Q
      simp only [Expectation.asRV_process]
      show Expectation.condEval (M θ) (fun ω k ↦ r k ω)
          (fun ω => (s t ω, a t ω))
          (fun integ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) (x, u) =
        ∫ ω, G ω ∂(M θ)[|B]
      rw [Expectation.condEval_eq_integral hpR hX hfG hmap, hpre]
      rfl
    have hcond :
        ∫ ω, G ω ∂(M θ)[|B] =
          ((M θ).real B)⁻¹ *
            ∫ ω, B.indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) ω * G ω ∂(M θ) := by
      rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hBm,
        ENNReal.toReal_inv, ← measureReal_def, smul_eq_mul]
      congr 1
      congr 1
      funext ω
      by_cases hω : ω ∈ B <;> simp [hω]
    rw [← hι1, hQ, hcond, ← mul_assoc, mul_inv_cancel₀ hQA, one_mul]

-- created on 2026-11-14
