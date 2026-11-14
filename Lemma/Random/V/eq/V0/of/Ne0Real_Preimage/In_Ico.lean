import Lemma.Random.MEq_V.of.In_Ico.All_Eq.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
On an atom of positive mass (`ℙ(s[t] = x) ≠ 0`): the observation form of the
state value agrees with the discounted `Wkd` series,
`V θ γ t x = V0 θ γ x`. When the state space is not discrete this may fail
at a particular `x` with `ℙ(s[t] = x) = 0`; the almost-everywhere form is
[V =ᵐ V0](?module=Random.MEq_V.of.In_Ico.All_Eq.All_EqWithDensity).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hP : (M θ).real ((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω t).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  M.V θ γ t x = M.V0 θ γ x := by
-- proof
  let r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω => (ω t).2.1
  let a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω => (ω t).2.2
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  have hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2) :=
    fun θ => M.policy.measurable_prob θ
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₁ t
  have hset : MeasurableSet (s t ⁻¹' ({x} : Set 𝒮)) :=
    hs (measurableSet_singleton x)
  have hpos : (M θ) (s t ⁻¹' ({x} : Set 𝒮)) ≠ 0 := by
    intro hz
    have hP' : (M θ).real (s t ⁻¹' ({x} : Set 𝒮)) ≠ 0 := hP
    apply hP'
    simp [Measure.real, hz]
  have hae :=
    MEq_V.of.In_Ico.All_Eq.All_EqWithDensity (M := M) h₀ h₁ hπ θ t
  have hnull : (M θ) {ω | M.V θ γ t (s t ω) ≠ M.V0 θ γ (s t ω)} = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using hae
  by_contra hne
  have hsubset :
      s t ⁻¹' ({x} : Set 𝒮) ⊆
        {ω | M.V θ γ t (s t ω) ≠ M.V0 θ γ (s t ω)} := by
    intro ω hω
    have hx : s t ω = x := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hω
    intro heq
    apply hne
    simpa [hx] using heq
  exact hpos (measure_mono_null hsubset hnull)


-- created on 2026-11-12
