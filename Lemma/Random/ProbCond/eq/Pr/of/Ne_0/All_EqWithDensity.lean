import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Conditional atom mass of a density policy:
`ℙ(a[t] = u | s[t] = x) = π_θ(u | x) * μ({u})` whenever `s[t] = x` has positive probability.
Continuous-action counterpart of `Random.ProbCond.eq.Pr.of.Ne_0`:
the regular conditional mass of the action atom equals the policy density times the
reference atom mass (both sides vanish when the reference measure is non-atomic).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (u : 𝒜) :
-- imply
  ((M θ)[|s t ⁻¹' {x}]).real (a t ⁻¹' {u}) =
    M.policy.prob θ x u * μ.measure.real {u} := by
-- proof
  have hS : MeasurableSet (s t ⁻¹' {x}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)
  have hA : MeasurableSet (a t ⁻¹' {u}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton u)
  have hSA : MeasurableSet (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) := hS.inter hA
  let φ : 𝒮 → 𝒜 → ℝ := fun y v => if y = x ∧ v = u then (1:ℝ) else 0
  have hφ : StronglyMeasurable (Function.uncurry φ) := by
    have h' :=
      (stronglyMeasurable_const (b := (1:ℝ))).indicator
        (measurableSet_singleton (x, u))
    have heq : Function.uncurry φ =
        ({(x, u)} : Set (𝒮 × 𝒜)).indicator (fun _ => (1:ℝ)) := by
      funext z
      rcases z with ⟨y, v⟩
      by_cases hy : y = x <;> by_cases hv : v = u <;>
        simp [φ, Function.uncurry, Set.indicator, hy, hv]
    rwa [heq]
  have hφC : ∀ y v, ‖φ y v‖ ≤ (1:ℝ) :=
    fun y v => by
      by_cases h : y = x ∧ v = u <;> simp [φ, h]
  rw [measureReal_def,
    cond_apply hS,
    ENNReal.toReal_mul,
    ENNReal.toReal_inv,
    ← measureReal_def,
    ← measureReal_def]
  have hnum :
      (M θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) =
        (M θ).real (s t ⁻¹' {x}) *
          (M.policy.prob θ x u * μ.measure.real {u}) := by
    have hind :
        (s t ⁻¹' {x} ∩ a t ⁻¹' {u}).indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) =
          fun ω => φ (s t ω) (a t ω) := by
      funext ω
      by_cases hsx : s t ω = x <;> by_cases hau : a t ω = u <;>
        simp [hsx, hau, φ, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
    rw [← integral_indicator_one hSA, hind,
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        h₀ hφ hφC θ t]
    have hinner : ∀ y,
        ∫ v, M.policy.prob θ y v • φ y v ∂μ.measure =
          (if y = x then (1:ℝ) else 0) *
            (M.policy.prob θ x u * μ.measure.real {u}) := by
      intro y
      by_cases hy : y = x
      · simp only [hy, φ, true_and, smul_eq_mul]
        have hfun :
            (fun v => M.policy.prob θ x v * (if v = u then (1:ℝ) else 0)) =
              ({u} : Set 𝒜).indicator (M.policy.prob θ x) := by
          funext v
          by_cases hv : v = u <;> simp [hv, Set.indicator]
        rw [hfun, integral_indicator (measurableSet_singleton u),
          Measure.restrict_singleton, integral_smul_measure,
          integral_dirac (M.policy.prob θ x) u, smul_eq_mul,
          mul_comm, measureReal_def]
        simp
      · simp [φ, hy]
    simp_rw [hinner, integral_mul_const]
    have hχ :
        (fun y : 𝒮 => (if y = x then (1:ℝ) else 0)) =
          ({x} : Set 𝒮).indicator 1 := by
      funext y
      by_cases hy : y = x <;> simp [hy, Set.indicator]
    rw [hχ, integral_indicator_one (measurableSet_singleton x),
      measureReal_def,
      Measure.map_apply (Random.Measurable.of.All_Eq.snd.fst h₀ t)
        (measurableSet_singleton x),
      ← measureReal_def]
  rw [hnum, inv_mul_cancel_left₀ h₁]


-- created on 2026-11-14
