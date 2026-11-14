import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.All_EqWithDensity.In_Ico
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable_G.of.All_Measurable
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Filter


/--
The discounted observational state value is the policy average of the action
values `Q` given by `h₂`. Here `Q` is the regular conditional (`condEval` /
`𝔼[G | s t = x ∧ a t = u]`), not the elementary atom conditional: on a
continuous action space those atoms are typically null, so the elementary
form would make the right-hand side vanish while the left-hand side need
not. When `ℙ(s[t] = x) = 0`, both sides are zero.
The discount factor is taken in `[0, 1)` (for `γ = 1` the Lean `tsum` of a
divergent series is `0` and the identity fails).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {Q : 𝒮 → 𝒜 → ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Q x u = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x ∧ a t = u))
  (x : 𝒮) :
-- imply
  ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] =
    ∫ ω, Q x (a t ω) ∂(M θ)[|s t ⁻¹' {x}] := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set G : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := (γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]
  set B : Set (ℕ → ℝ × 𝒮 × 𝒜) := s t ⁻¹' {x}
  set Y : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 × 𝒜 := fun ω => (s t ω, a t ω)
  set BG : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hGeq : ∀ ω, G ω = ∑' k, γ ^ k * r (t + k) ω := by
    intro ω
    simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
  if hB0 : (M θ) B = 0 then
    simp [cond_eq_zero_of_meas_eq_zero hB0]
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB0
    have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₁ t
    have ha : Measurable (a t) := Random.Measurable.of.All_Eq.snd.snd h₁ t
    have hY : Measurable Y := hs.prodMk ha
    have hBset : MeasurableSet B := hs (measurableSet_singleton x)
    have hG : ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|B] =
        ∫ ω, G ω ∂(M θ)[|B] :=
      integral_congr_ae (Eventually.of_forall fun ω => (hGeq ω).symm)
    rw [hG]
    unfold ProbabilityTheory.cond
    simp only [integral_smul_measure, smul_eq_mul]
    congr 1
    have hGm : Measurable G := by
      have hfun : G = fun ω => ∑' k, γ ^ k * r (t + k) ω := by
        ext ω
        exact hGeq ω
      rw [hfun]
      exact Measurable.tsum fun k =>
        (Random.Measurable.of.All_Eq.fst h₁ (t + k)).const_mul (γ ^ k)
    have hGbd : ∀ᵐ ω ∂(M θ), ‖G ω‖ ≤ BG := by
      filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hrω
      have hsum : Summable fun k => γ ^ k * |M.env.R| :=
        (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
      have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
        simpa [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left (hrω (t + k)) (pow_nonneg h₀.1 k)
      have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
        Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
      rw [hGeq]
      calc
        _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
        _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
        _ = BG := by
          rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
    have hGint : Integrable G (M θ) :=
      Integrable.of_bound hGm.aestronglyMeasurable BG hGbd
    have hg : StronglyMeasurable
      (fun path : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:]) :=
      (Measurable_G.of.All_Measurable
        (r := fun j (path : ℕ → ℝ) => path j)
        (fun j => measurable_pi_apply j) γ t).stronglyMeasurable
    have hpath : Measurable (AsPathRV.path r) :=
      Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
    have hQae : (fun ω => Q (s t ω) (a t ω)) =ᵐ[M θ]
        condExp (MeasurableSpace.comap Y inferInstance) (M θ) G := by
      have hae :=
        Expectation.condEval_comp_ae_eq_condSigma
          (π := M θ) (x := AsPathRV.path r) (y := Y)
          (f := fun path ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:])
          hpath.aemeasurable hY hg hGint
      have hdef : (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun k => r k ω)[t:]) = G := by
        ext ω
        simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
      have hYj : (s t, a t) = Y := rfl
      filter_upwards [hae] with ω hω
      have hQω : Q (s t ω) (a t ω) =
          Expectation.condEval (M θ) (AsPathRV.path r) (s t, a t)
            (fun path ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:]) (s t ω, a t ω) := by
        simpa [Expectation.asRV_process] using h₂ (s t ω) (a t ω)
      rw [hQω, hYj, hω]
      simp only [Expectation.condSigma, AsPathRV.path_process, hdef]
    have hQonB : ∀ᵐ ω ∂(M θ), ω ∈ B → Q x (a t ω) = Q (s t ω) (a t ω) :=
      Eventually.of_forall fun ω hω => by
        have hx : s t ω = x := by
          simpa [B, Set.mem_preimage, Set.mem_singleton_iff] using hω
        rw [hx]
    have hBcomap : MeasurableSet[MeasurableSpace.comap Y inferInstance] B :=
      (show B = Y ⁻¹' (({x} : Set 𝒮) ×ˢ Set.univ) by
        ext ω
        simp [B, Y, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]) ▸
      (MeasurableSet.preimage
        ((measurableSet_singleton x).prod (@MeasurableSet.univ 𝒜 inferInstance))
        (fun t ht => ⟨t, ht, rfl⟩))
    have : SigmaFinite ((M θ).trim hY.comap_le) := inferInstance
    rw [setIntegral_congr_ae hBset hQonB]
    rw [setIntegral_congr_ae hBset (hQae.mono fun ω hω _ => hω)]
    exact (setIntegral_condExp (hm := hY.comap_le) hGint hBcomap).symm


-- created on 2026-11-14
