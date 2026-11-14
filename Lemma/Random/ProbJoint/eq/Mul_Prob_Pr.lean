import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Joint law of state and action in the continuous-action trajectory model:
`ℙ(s[t] = x, a[t] = u) = ℙ(s[t] = x) * π_θ(u | x) * μ({u})`.
The action atom mass is the policy density times the reference atom mass
(both sides of the action factor vanish when the reference measure is non-atomic).
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
  (M θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) =
    (M θ).real (s t ⁻¹' {x}) * (M.policy.prob θ x u * μ.measure.real {u}) := by
-- proof
  have hS : MeasurableSet (s t ⁻¹' {x}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)
  have hA : MeasurableSet (a t ⁻¹' {u}) :=
    Random.Measurable.of.All_Eq.snd.snd h₀ t (measurableSet_singleton u)
  have hSA : MeasurableSet (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) := hS.inter hA
  have heq : (Function.uncurry fun (y : 𝒮) (v : 𝒜) =>
    if y = x ∧ v = u then (1:ℝ) else 0) =
    ({(x, u)} : Set (𝒮 × 𝒜)).indicator (fun _ => (1:ℝ)) := by
    funext z
    if h : z = (x, u) then
      subst h
      simp [Function.uncurry, Set.indicator]
    else
      have hz : ¬(z.1 = x ∧ z.2 = u) := fun h' => h (Prod.ext h'.1 h'.2)
      simp [Function.uncurry, Set.indicator, Set.mem_singleton_iff, h, hz]
  have hφ : StronglyMeasurable
    (Function.uncurry fun (y : 𝒮) (v : 𝒜) =>
      if y = x ∧ v = u then (1:ℝ) else 0) := by
    rw [heq]
    apply (stronglyMeasurable_const (b := (1:ℝ))).indicator
    apply measurableSet_singleton
  have hφC : ∀ y v,
    ‖(if y = x ∧ v = u then (1:ℝ) else 0)‖ ≤ (1:ℝ) :=
    fun y v => by
      by_cases h : y = x ∧ v = u <;> simp [h]
  have hind :
    (s t ⁻¹' {x} ∩ a t ⁻¹' {u}).indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) =
      fun ω => if s t ω = x ∧ a t ω = u then (1:ℝ) else 0 := by
    funext ω
    by_cases hsx : s t ω = x <;> by_cases hau : a t ω = u <;>
      simp [hsx, hau, Set.indicator, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
  rw [← integral_indicator_one hSA, hind,
    Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
      h₀ hφ hφC θ t]
  have hinner : ∀ y,
      ∫ v, M.policy.prob θ y v • (if y = x ∧ v = u then (1:ℝ) else 0)
        ∂μ.measure =
        (if y = x then (1:ℝ) else 0) *
          (M.policy.prob θ x u * μ.measure.real {u}) := by
    intro y
    if hy : y = x then
      subst hy
      simp only [true_and, smul_eq_mul]
      have hfun :
        (fun v => M.policy.prob θ y v * (if v = u then (1:ℝ) else 0)) =
          ({u} : Set 𝒜).indicator (M.policy.prob θ y) := by
        funext v
        by_cases hv : v = u <;> simp [hv, Set.indicator]
      rw [hfun, integral_indicator (measurableSet_singleton u),
        Measure.restrict_singleton, integral_smul_measure]
      simp [integral_dirac, smul_eq_mul, measureReal_def, mul_comm]
    else
      simp [hy]
  simp_rw [hinner, integral_mul_const]
  have hχ :
    (fun y : 𝒮 => (if y = x then (1:ℝ) else 0)) =
      ({x} : Set 𝒮).indicator 1 := by
    funext y
    by_cases hy : y = x <;> simp [hy, Set.indicator]
  rw [hχ, integral_indicator_one (measurableSet_singleton x)]
  simp [measureReal_def,
    Measure.map_apply (Random.Measurable.of.All_Eq.snd.fst h₀ t)
      (measurableSet_singleton x)]


-- created on 2026-09-26
-- updated on 2026-11-14
