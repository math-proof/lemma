import Lemma.Random.ExpectSMul.eq.ExpectSMulExpectCond.of.All_LeNorm.StronglyMeasurable.All_Eq.All_EqWithDensity.In_Ico
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.PSpace_Path.of.All_PSpace
import Mathlib.Analysis.Calculus.Gradient.Basic
import Def.Analysis.Calculus.Gradient.Operators.Part2
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Filter Topology Measure
open scoped ENNReal.ToRealCoe


/--
`𝔼[∇ log π(a[t] | s[t]) • (γ ** ⬝ᵥ r[t:])] =
  𝔼[∇ log π(a[t] | s[t]) • 𝔼[(γ ** ⬝ᵥ r[t:]) | s[t], a[t]]]`
(law of iterated expectation on `(s[t], a[t])`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {C : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜} [∀ θ t, SinglePSpace (M θ) (a t, s t)]
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hψ : StronglyMeasurable (fun p : 𝒮 × 𝒜 =>
    ∇[θ] (ℙ[M θ]((a t) = p.2 | (s t) = p.1) : ℝ).log))
  (hC : ∀ x u, ‖∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log‖ ≤ C) :
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
  let : MeasurableSpace Θ := borel Θ
  𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
    𝔼[s, a : M θ](
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t], a[t]) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
-- proof
  intro _ _ _
  let _ : MeasurableSpace Θ := borel Θ
  let ψ : 𝒮 → 𝒜 → Θ := fun x u =>
    ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log
  have hψ' : StronglyMeasurable (Function.uncurry ψ) := by
    change StronglyMeasurable (fun p : 𝒮 × 𝒜 => ψ p.1 p.2)
    simpa [ψ] using hψ
  convert
    ExpectSMul.eq.ExpectSMulExpectCond.of.All_LeNorm.StronglyMeasurable.All_Eq.All_EqWithDensity.In_Ico
      (M := M) (ψ := ψ) h₀ h₁ hψ' hC θ t


-- created on 2026-11-14
