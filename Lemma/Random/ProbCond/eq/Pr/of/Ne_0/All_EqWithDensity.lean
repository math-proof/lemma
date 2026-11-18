import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


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
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {t : ℕ}
  {sₜ : 𝒮}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : (M θ).real (s t ⁻¹' {sₜ}) ≠ 0)
  (aₜ : 𝒜) :
-- imply
  ((M θ)[|s t ⁻¹' {sₜ}]).real (a t ⁻¹' {aₜ}) =
    M.π[θ] sₜ aₜ * μ.measure.real {aₜ} := by
-- proof
  have hS : MeasurableSet (s t ⁻¹' {sₜ}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton sₜ)
  have hA : MeasurableSet (a t ⁻¹' {aₜ}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton aₜ)
  have hSA : MeasurableSet (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}) := hS.inter hA
  let φ : 𝒮 → 𝒜 → ℝ := fun y v => if y = sₜ ∧ v = aₜ then (1:ℝ) else 0
  have hφ : StronglyMeasurable (Function.uncurry φ) := by
    have h' :=
      (stronglyMeasurable_const (b := (1:ℝ))).indicator
        (measurableSet_singleton (sₜ, aₜ))
    have heq : Function.uncurry φ =
        ({(sₜ, aₜ)} : Set (𝒮 × 𝒜)).indicator (fun _ => (1:ℝ)) := by
      funext z
      rcases z with ⟨y, v⟩
      by_cases hy : y = sₜ <;> by_cases hv : v = aₜ <;>
        simp [φ, Function.uncurry, Set.indicator, hy, hv]
    rwa [heq]
  have hφC : ∀ y v, ‖φ y v‖ ≤ (1:ℝ) :=
    fun y v => by
      by_cases h : y = sₜ ∧ v = aₜ <;> simp [φ, h]
  rw [measureReal_def,
    cond_apply hS,
    ENNReal.toReal_mul,
    ENNReal.toReal_inv,
    ← measureReal_def,
    ← measureReal_def]
  have hnum :
      (M θ).real (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}) =
        (M θ).real (s t ⁻¹' {sₜ}) *
          (M.π[θ] sₜ aₜ * μ.measure.real {aₜ}) := by
    have hind :
        (s t ⁻¹' {sₜ} ∩ a t ⁻¹' {aₜ}).indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) =
          fun ω => φ (s t ω) (a t ω) := by
      funext ω
      by_cases hsx : s t ω = sₜ <;> by_cases hau : a t ω = aₜ <;>
        simp [hsx, hau, φ, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
    rw [← integral_indicator_one hSA, hind,
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        h₀ hφ hφC θ t]
    have hinner : ∀ y,
        ∫ v, M.π[θ] y v • φ y v ∂μ.measure =
          (if y = sₜ then (1:ℝ) else 0) *
            (M.π[θ] sₜ aₜ * μ.measure.real {aₜ}) := by
      intro y
      by_cases hy : y = sₜ
      · simp only [hy, φ, true_and, smul_eq_mul]
        have hfun :
            (fun v => M.π[θ] sₜ v * (if v = aₜ then (1:ℝ) else 0)) =
              ({aₜ} : Set 𝒜).indicator (M.π[θ] sₜ) := by
          funext v
          by_cases hv : v = aₜ <;> simp [hv, Set.indicator]
        rw [hfun, integral_indicator (measurableSet_singleton aₜ),
          Measure.restrict_singleton, integral_smul_measure,
          integral_dirac (M.π[θ] sₜ) aₜ, smul_eq_mul,
          mul_comm, measureReal_def]
        simp
      · simp [φ, hy]
    simp_rw [hinner, integral_mul_const]
    have hχ :
        (fun y : 𝒮 => (if y = sₜ then (1:ℝ) else 0)) =
          ({sₜ} : Set 𝒮).indicator 1 := by
      funext y
      by_cases hy : y = sₜ <;> simp [hy, Set.indicator]
    rw [hχ, integral_indicator_one (measurableSet_singleton sₜ),
      measureReal_def,
      Measure.map_apply (Random.Measurable.of.All_Eq.snd.fst h₀ t)
        (measurableSet_singleton sₜ),
      ← measureReal_def]
  rw [hnum, inv_mul_cancel_left₀ h₁]


-- created on 2026-11-14
-- updated on 2026-11-18