import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.Measurable_G.of.All_Measurable
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Lemma.Random.PSpace_Path.of.All_PSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Kernel.CondDistrib
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Filter Measure


/--
`𝔼[G[t] • ψ(s[t], a[t])] = 𝔼[𝔼[G[t] | s[t], a[t]] • ψ(s[t], a[t])]`
under the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ C : ℝ}
  {ψ : 𝒮 → 𝒜 → E}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hC : ∀ y u, ‖ψ y u‖ ≤ C)
  (θ : Θ)
  (t : ℕ) :
-- imply
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) • ψ (s t) (a t)) =
    𝔼[s, a : M θ](
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t], a[t]) • ψ (s t) (a t)) := by
-- proof
  intro _ _ _
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  set G := (γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]
  set BG : ℝ := (1 - γ)⁻¹ * |M.env.R|
  set Y := fun ω => (s t ω, a t ω)
  have hBG : 0 ≤ BG :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hCle : ∀ y u, ‖ψ y u‖ ≤ max C 0 := fun y u => (hC y u).trans (le_max_left _ _)
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₁ t
  have ha : Measurable (a t) := Random.Measurable.of.All_Eq.snd.snd h₁ t
  have hY : Measurable Y := hs.prodMk ha
  have hGeq : ∀ ω, G ω = ∑' k, γ ^ k * r (t + k) ω := by
    intro ω
    simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
  have hGbd : ∀ᵐ ω ∂(M θ), ‖G ω‖ ≤ BG := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hrω
    have hsum : Summable fun k => γ ^ k * |M.env.R| :=
      (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hrω (t + k))
        (pow_nonneg h₀.1 k)
    have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
    rw [hGeq]
    calc
      _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
      _ = BG := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
  have hGm : Measurable G := by
    have hfun : G = fun ω => ∑' k, γ ^ k * r (t + k) ω := by
      ext ω
      exact hGeq ω
    rw [hfun]
    exact Measurable.tsum fun k =>
      (Random.Measurable.of.All_Eq.fst h₁ (t + k)).const_mul (γ ^ k)
  have hψY : StronglyMeasurable (fun ω => ψ (s t ω) (a t ω)) :=
    hψ.comp_measurable hY
  have hGint : Integrable G (M θ) :=
    Integrable.of_bound hGm.aestronglyMeasurable BG hGbd
  have hLint : Integrable (fun ω => G ω • ψ (s t ω) (a t ω)) (M θ) :=
    Integrable.of_bound (hGm.stronglyMeasurable.smul hψY).aestronglyMeasurable
      (BG * max C 0)
      (hGbd.mono fun ω hω => by
        rw [norm_smul]
        exact mul_le_mul hω (hCle _ _) (norm_nonneg _) hBG)
  have hsa3 : Measurable fun p : (ℕ → ℝ) × ((ℕ → 𝒮) × (ℕ → 𝒜)) ↦ (p.2.1 t, p.2.2 t) :=
    ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
  have hGpath : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → 𝒮) × (ℕ → 𝒜)) ↦
      ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ p.1 (t + k)) :=
    (Measurable_G.of.All_Measurable
      (r := fun j (p : (ℕ → ℝ) × ((ℕ → 𝒮) × (ℕ → 𝒜))) => p.1 j)
      (fun j => (measurable_pi_apply j).comp measurable_fst) γ t).stronglyMeasurable
  have hψpath3 : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → 𝒮) × (ℕ → 𝒜)) ↦
      ψ (p.2.1 t) (p.2.2 t) :=
    hψ.comp_measurable hsa3
  have hsa : Measurable fun p : (ℕ → 𝒮) × (ℕ → 𝒜) ↦ (p.1 t, p.2 t) :=
    ((measurable_pi_apply t).comp measurable_fst).prodMk
      ((measurable_pi_apply t).comp measurable_snd)
  have hL :
    𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) • ψ (s t) (a t)) =
      ∫ ω, G ω • ψ (s t ω) (a t ω) ∂(M θ) := by
    apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    exact (hGpath.smul hψpath3).aestronglyMeasurable
  have hg : StronglyMeasurable
    (fun path : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:]) :=
    (Measurable_G.of.All_Measurable
      (r := fun j (path : ℕ → ℝ) => path j)
      (fun j => measurable_pi_apply j) γ t).stronglyMeasurable
  have hEval : StronglyMeasurable
    (fun q : 𝒮 × 𝒜 ↦
      Expectation.condEval (M θ) (AsPathRV.path r) Y
        (fun path ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:]) q) := by
    simp only [Expectation.condEval]
    have hf : StronglyMeasurable
      (fun z : Prod (𝒮 × 𝒜) (ℕ → ℝ) ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ z.2[t:]) :=
      hg.comp_measurable measurable_snd
    exact hf.integral_condDistrib (Y := AsPathRV.path r) (X := Y) (μ := M θ)
  have hR :
    𝔼[s, a : M θ](
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t], a[t]) • ψ (s t) (a t)) =
      ∫ ω, condExp (MeasurableSpace.comap Y inferInstance) (M θ) G ω •
        ψ (s t ω) (a t ω) ∂(M θ) := by
    have h := OfRV.eq.Integral.of.AEStronglyMeasurable_Map
      (π := M θ) (x := (AsPathRV.path s, AsPathRV.path a))
      (f := fun p : (ℕ → 𝒮) × (ℕ → 𝒜) ↦
        Expectation.condEval (M θ) (AsPathRV.path r) Y
          (fun path ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:]) (p.1 t, p.2 t) •
          ψ (p.1 t) (p.2 t))
      ((hEval.smul hψ).comp_measurable hsa).aestronglyMeasurable
    refine h.trans (integral_congr_ae ?_)
    have hae :=
      Expectation.condEval_comp_ae_eq_condSigma
        (π := M θ) (x := AsPathRV.path r) (y := Y)
        (f := fun path ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:])
        PSpace.aemeasurable hY hg hGint
    have hdef :
      Expectation.condSigma (M θ) (AsPathRV.path r) Y
        (fun path ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:]) =
        condExp (MeasurableSpace.comap Y inferInstance) (M θ) G := by
      simp only [Expectation.condSigma, G]
      rfl
    filter_upwards [hae] with ω hω
    simp only [JointRandomSymbol, AsPathRV.path_process, Y] at hω hdef ⊢
    rw [hω, hdef]
  have hψm :
    AEStronglyMeasurable[MeasurableSpace.comap Y inferInstance]
      (fun ω => ψ (s t ω) (a t ω)) (M θ) :=
    (hψ.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable
  have hpull :
    condExp (MeasurableSpace.comap Y inferInstance) (M θ)
      (fun ω => G ω • ψ (s t ω) (a t ω)) =ᵐ[M θ]
      fun ω =>
        condExp (MeasurableSpace.comap Y inferInstance) (M θ) G ω •
          ψ (s t ω) (a t ω) :=
    condExp_smul_of_aestronglyMeasurable_right
      (m := MeasurableSpace.comap Y inferInstance) (μ := M θ) hGint hLint hψm
  refine hL.trans (Eq.trans ?_ hR.symm)
  have : SigmaFinite ((M θ).trim hY.comap_le) := inferInstance
  calc
    _ = ∫ ω,
        condExp (MeasurableSpace.comap Y inferInstance) (M θ)
          (fun ω => G ω • ψ (s t ω) (a t ω)) ω ∂(M θ) :=
      (integral_condExp (hm := hY.comap_le) (μ := M θ)
        (f := fun ω => G ω • ψ (s t ω) (a t ω))).symm
    _ = ∫ ω,
        condExp (MeasurableSpace.comap Y inferInstance) (M θ) G ω •
          ψ (s t ω) (a t ω) ∂(M θ) :=
      integral_congr_ae hpull


-- created on 2026-11-14
