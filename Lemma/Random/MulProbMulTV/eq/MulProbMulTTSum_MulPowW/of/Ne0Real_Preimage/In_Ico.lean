import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS.of.All_EqWithDensity
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.All_EqWithDensity.In_Ico
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral_MulEqAndEq.eq.MulMulRealProbSum_MulT.of.All_Eq
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
On a reachable state `x`:
`π_θ(u | x) * μ({u}) * T(x, u, {y}) * V θ γ (t+1) y
= π_θ(u | x) * μ({u}) * T(x, u, {y}) * ∑' k, γ ^ k * W θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k y`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (u : 𝒜)
  (y : 𝒮) :
-- imply
  let V (θ : Θ) (t : ℕ) (x : 𝒮) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x);
  M.policy.prob θ x u * μ.measure.real {u} * (M.env.trans (x, u)).real {y} * V θ (t + 1) y =
    M.policy.prob θ x u * μ.measure.real {u} * (M.env.trans (x, u)).real {y} *
      ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
        ∂(M.stageK θ y) := by
-- proof
  intro Vθ
  if hz : M.policy.prob θ x u * μ.measure.real {u} *
      (M.env.trans (x, u)).real {y} = 0 then
    simp [hz]
  else
    obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
      funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
    obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
      funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
    set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
    set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
    have hfY : StronglyMeasurable
      (fun y' : 𝒮 => if y' = y then (1:ℝ) else 0) :=
      StronglyMeasurable.of_discrete
    have hCY : ∀ y' : 𝒮, ‖if y' = y then (1:ℝ) else 0‖ ≤ (1:ℝ) :=
      fun y' => by
        if hy' : y' = y then
          simp [hy']
        else
          simp [hy']
    have hint : ∫ y', (if y' = y then (1:ℝ) else 0) ∂(M.env.trans (x, u)) =
        (M.env.trans (x, u)).real {y} := by
      have hfeq : (fun y' : 𝒮 => if y' = y then (1:ℝ) else 0) =
          ({y} : Set 𝒮).indicator (1 : 𝒮 → ℝ) := by
        funext y'
        if hy' : y' = y then
          simp [Set.indicator, hy']
        else
          simp [Set.indicator, hy']
      rw [hfeq, integral_indicator_one (measurableSet_singleton y)]
    have hE :
      ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
          (if s (t + 1) ω = y then (1:ℝ) else 0) ∂(M θ) =
        (M θ).real (s t ⁻¹' {x}) *
          (M.policy.prob θ x u * μ.measure.real {u}) *
          (M.env.trans (x, u)).real {y} := by
      rw [Integral_MulEqAndEq.eq.MulMulRealProbSum_MulT.of.All_Eq
        (M := M) h₁ hfY hCY θ t x u, hint]
    have hS : MeasurableSet (s t ⁻¹' {x}) :=
      Random.Measurable.of.All_Eq.snd.fst h₁ t (measurableSet_singleton x)
    have hA : MeasurableSet (a t ⁻¹' {u}) :=
      Random.Measurable.of.All_Eq.snd.snd h₁ t (measurableSet_singleton u)
    have hY : MeasurableSet (s (t + 1) ⁻¹' {y}) :=
      Random.Measurable.of.All_Eq.snd.fst h₁ (t + 1)
        (measurableSet_singleton y)
    have hSA : MeasurableSet (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) := hS.inter hA
    have hindp :
      (fun ω =>
        (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
          (if s (t + 1) ω = y then (1:ℝ) else 0)) =
        (s t ⁻¹' {x} ∩ a t ⁻¹' {u} ∩ s (t + 1) ⁻¹' {y}).indicator
          (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) := by
      funext ω
      if hsx : s t ω = x then
        if hau : a t ω = u then
          if hsy : s (t + 1) ω = y then
            simp [hsx, hau, hsy, Set.indicator, Set.mem_inter_iff,
              Set.mem_preimage, Set.mem_singleton_iff]
          else
            simp [hsx, hau, hsy, Set.indicator, Set.mem_inter_iff,
              Set.mem_preimage, Set.mem_singleton_iff]
        else
          simp [hsx, hau, Set.indicator, Set.mem_inter_iff,
            Set.mem_preimage, Set.mem_singleton_iff]
      else
        simp [hsx, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
    have hle :
      ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
          (if s (t + 1) ω = y then (1:ℝ) else 0) ∂(M θ) ≤
        (M θ).real (s (t + 1) ⁻¹' {y}) := by
      rw [hindp, integral_indicator_one (hSA.inter hY)]
      exact measureReal_mono (fun ω hω => hω.2)
    have hpos : 0 <
        (M θ).real (s t ⁻¹' {x}) *
          (M.policy.prob θ x u * μ.measure.real {u}) *
          (M.env.trans (x, u)).real {y} := by
      apply mul_pos
      ·
        apply mul_pos
        · exact lt_of_le_of_ne measureReal_nonneg (Ne.symm hP)
        exact lt_of_le_of_ne
          (mul_nonneg (M.policy.nonneg θ x u) measureReal_nonneg)
          (fun h0 => hz (by rw [← h0, zero_mul]))
      exact lt_of_le_of_ne measureReal_nonneg
        (fun h0 => hz (by rw [← h0, mul_zero]))
    have hPy : (M θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 := by
      intro h0
      have hle' := hle
      rw [hE, h0] at hle'
      exact (not_le_of_gt hpos) hle'
    have hclip : StronglyMeasurable
      (fun z : ℝ × 𝒮 × 𝒜 ↦ clip z.1 (-M.env.R) M.env.R) := by
      unfold clip
      apply
        ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
    have hclipbound : ∀ z : ℝ × 𝒮 × 𝒜,
        ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
      fun z => NormClip.le.Abs_R M.env.R z.1
    have hGx : StronglyMeasurable
      (fun z : ℝ × 𝒮 × 𝒜 => if z.2.1 = y then (1:ℝ) else 0) :=
      (StronglyMeasurable.of_discrete
        (f := fun y' : 𝒮 => if y' = y then (1:ℝ) else 0)).comp_measurable
        measurable_snd.fst
    have hGxbound : ∀ z : ℝ × 𝒮 × 𝒜,
        ‖if z.2.1 = y then (1:ℝ) else 0‖ ≤ (1:ℝ) :=
      fun z => by
        if hz' : z.2.1 = y then
          simp [hz']
        else
          simp [hz']
    have hSW : ∀ k,
        ∫ ω, (if s (t + 1) ω = y then (1:ℝ) else 0) *
            r (t + 1 + k) ω ∂(M θ) =
          (M θ).real (s (t + 1) ⁻¹' {y}) *
            ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
              ∂(M.stageK θ y) := by
      intro k
      have hrc :
        ∫ ω, (if s (t + 1) ω = y then (1:ℝ) else 0) *
            r (t + 1 + k) ω ∂(M θ) =
          ∫ ω, (if s (t + 1) ω = y then (1:ℝ) else 0) *
            clip (ω (t + 1 + k)).1 (-M.env.R) M.env.R ∂(M θ) :=
        integral_congr_ae
          ((MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ (t + 1 + k)).mono
            fun ω h => by
              dsimp only
              rw [h])
      have hK :=
        StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hclip hclipbound θ k
      rw [hrc,
        Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hclip hclipbound hGx hGxbound θ (t + 1) k,
        Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          h₁ (M := M) hK.1 hK.2 θ (t + 1) y]
    have hV : Vθ θ (t + 1) y =
        ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
          ∂(M.stageK θ y) := by
      dsimp only [Vθ]
      have hpR : Measurable (fun ω t ↦ r t ω) :=
        Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
      have hs : Measurable (s (t + 1)) :=
        Random.Measurable.of.All_Eq.snd.fst h₁ (t + 1)
      have hfG : Measurable
        (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t + 1:]) :=
        Measurable.tsum fun k =>
          (measurable_pi_apply (t + 1 + k)).const_mul _
      have hmap : (M θ).map (s (t + 1)) {y} ≠ 0 := by
        rwa [Measure.map_apply hs (measurableSet_singleton y),
          ← measureReal_ne_zero_iff]
      simp only [Expectation.asRV_process]
      rw [Expectation.condEval_eq_integral hpR hs hfG hmap]
      show ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t + 1:]) ω
        ∂(M θ)[|s (t + 1) ⁻¹' {y}] = _
      rw [Integral_G.eq.TSum_MulPowIntegral_R_Add.of.All_EqWithDensity.In_Ico
        (M := M) h₀ h₁ θ (s (t + 1) ⁻¹' {y}) (t + 1)]
      congr 1
      funext k
      rw [Integral.eq.MulRealPreimageSIntegral_MulEqS.of.All_EqWithDensity h₁,
        hSW k, inv_mul_cancel_left₀ hPy]
    rw [hV]


-- created on 2026-10-07
-- updated on 2026-11-14
