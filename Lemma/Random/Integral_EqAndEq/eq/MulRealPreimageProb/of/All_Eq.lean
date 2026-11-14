import Lemma.Random.ProbJoint.eq.Mul_Prob_Pr
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real


/--
Joint law of state and action in the continuous-action trajectory model,
written as an integral of the atom indicator:
`𝔼[1{s[t] = x ∧ a[t] = u}] = ℙ(s[t] = x) * π_θ(u | x) * μ({u})`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {t : ℕ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * (M.policy.prob θ x u * μ.measure.real {u}) := by
-- proof
  have hS : MeasurableSet (s t ⁻¹' {x}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)
  have hA : MeasurableSet (a t ⁻¹' {u}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton u)
  have hSA : MeasurableSet (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) := hS.inter hA
  have hind :
    (s t ⁻¹' {x} ∩ a t ⁻¹' {u}).indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) =
      fun ω => if s t ω = x ∧ a t ω = u then (1:ℝ) else 0 := by
    funext ω
    by_cases hsx : s t ω = x <;> by_cases hau : a t ω = u <;>
      simp [hsx, hau, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
  rw [← hind, integral_indicator_one hSA]
  apply ProbJoint.eq.Mul_Prob_Pr h₀


-- created on 2026-10-07
-- updated on 2026-11-14
