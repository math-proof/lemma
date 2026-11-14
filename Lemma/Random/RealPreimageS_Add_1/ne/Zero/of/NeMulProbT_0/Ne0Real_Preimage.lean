import Lemma.Random.Integral_MulEqAndEq.eq.MulMulRealProbSum_MulT.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Reachability in the continuous-action trajectory model: if `ℙ(s[t] = x) ≠ 0` and
`π_θ(u | x) * μ({u}) * T(x, u, {y}) ≠ 0` then `ℙ(s[t+1] = y) ≠ 0`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
  {u : 𝒜}
  {y : 𝒮}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (hz : M.policy.prob θ x u * μ.measure.real {u} *
    (M.env.trans (x, u)).real {y} ≠ 0) :
-- imply
  (M θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 := by
-- proof
  have hfeq : (fun y' : 𝒮 => if y' = y then (1:ℝ) else 0) =
      ({y} : Set 𝒮).indicator (1 : 𝒮 → ℝ) := by
    funext y'
    if hy' : y' = y then
      simp [Set.indicator, hy']
    else
      simp [Set.indicator, hy']
  have hfY : StronglyMeasurable
    (fun y' : 𝒮 => if y' = y then (1:ℝ) else 0) := by
    rw [hfeq]
    exact (stronglyMeasurable_const (b := (1:ℝ))).indicator
      (measurableSet_singleton y)
  have hCY : ∀ y' : 𝒮, ‖if y' = y then (1:ℝ) else 0‖ ≤ (1:ℝ) :=
    fun y' => by
      if hy' : y' = y then
        simp [hy']
      else
        simp [hy']
  have hint : ∫ y', (if y' = y then (1:ℝ) else 0) ∂(M.env.trans (x, u)) =
      (M.env.trans (x, u)).real {y} := by
    rw [hfeq, integral_indicator_one (measurableSet_singleton y)]
  have hE :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (if s (t + 1) ω = y then (1:ℝ) else 0) ∂(M θ) =
      (M θ).real (s t ⁻¹' {x}) *
        (M.policy.prob θ x u * μ.measure.real {u}) *
        (M.env.trans (x, u)).real {y} := by
    rw [Integral_MulEqAndEq.eq.MulMulRealProbSum_MulT.of.All_Eq
      (M := M) h₀ hfY hCY θ t x u, hint]
  have hS : MeasurableSet (s t ⁻¹' {x}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)
  have hA : MeasurableSet (a t ⁻¹' {u}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton u)
  have hY : MeasurableSet (s (t + 1) ⁻¹' {y}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ (t + 1)
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
  intro h0
  rw [hE, h0] at hle
  exact (not_le_of_gt hpos) hle


-- created on 2026-10-07
-- updated on 2026-11-14
