import Lemma.Random.Map.eq.BindStageK.of.All_EqWithDensity
import Lemma.Random.EqMapStageK_12.of.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Initial state under the continuous-action trajectory model is `env.init`:
`law(s[0]) = env.init`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
-- imply
  (M θ).map (s 0) = M.env.init := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  have : (M θ).map (s 0) = ((M θ).map (fun ω ↦ ω 0)).map (fun z ↦ z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply 0)]; rfl
  rw [this, Map.eq.BindStageK.of.All_EqWithDensity,
    EqMapStageK_12.of.All_EqWithDensity]


-- created on 2026-10-20
