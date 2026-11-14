import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
open MeasureTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Sanity check: `𝔼[state, action, reward : M θ](…)` elaborates by flipping each process to its path RV
(`AsPathRV.process`) and taking their finite joint law.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  have hs : ∀ t, PSpace (M θ) (s t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.fst h₀ t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (a t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.snd h₀ t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₀ t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace hs
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace ha
  have : PSpace (M θ) (AsPathRV.path r) :=
    PSpace_Path.of.All_PSpace hr
  𝔼[r, s, a : M θ](∑' t, γ ^ t * r t) =
    ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ) := by
-- proof
  intro _ _ _ _ _ _
  exact OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun p : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜) => ∑' t, γ ^ t * p.1 t)
    ((Measurable.tsum fun t => ((measurable_pi_apply t).comp measurable_fst).const_mul _).aestronglyMeasurable)


-- created on 2026-09-28
-- updated on 2026-11-14
