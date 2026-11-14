import Lemma.Random.ProbJoint.eq.Mul_Prob_Pr
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * φ(s[t], a[t])] = ℙ(s[t] = x) * π_θ(u | x) * μ({u}) * φ x u`
in the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : 𝒮)
  (u : 𝒜)
  (φ : 𝒮 → 𝒜 → ℝ) :
-- imply
  ∫ ω, (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1:ℝ) else 0) * φ (ω t).2.1 (ω t).2.2 ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * (M.policy.prob θ x u * μ.measure.real {u}) * φ x u := by
-- proof
  have h₂ : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
      (if (ω t).2.1 = x ∧ (ω t).2.2 = u then (1:ℝ) else 0) * φ (ω t).2.1 (ω t).2.2 =
        (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * φ x u := by
    intro ω
    have hs : s t ω = (ω t).2.1 := (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
    have ha : a t ω = (ω t).2.2 := (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
    simp only [hs, ha]
    if h1 : (ω t).2.1 = x then
      if h2 : (ω t).2.2 = u then
        simp [h1, h2]
      else
        simp [h1, h2]
    else
      simp [h1]
  simp_rw [h₂]
  rw [integral_mul_const]
  have hS : MeasurableSet (s t ⁻¹' {x}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)
  have hA : MeasurableSet (a t ⁻¹' {u}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton u)
  have hSA : MeasurableSet (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) := hS.inter hA
  have hind :
    (s t ⁻¹' {x} ∩ a t ⁻¹' {u}).indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) =
      fun ω => if s t ω = x ∧ a t ω = u then (1:ℝ) else 0 := by
    funext ω
    if hsx : s t ω = x then
      if hau : a t ω = u then
        simp [hsx, hau, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
      else
        simp [hsx, hau, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
    else
      simp [hsx, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
  rw [← hind, integral_indicator_one hSA, ProbJoint.eq.Mul_Prob_Pr (M := M) h₀ x u]


-- created on 2026-10-07
-- updated on 2026-11-14
