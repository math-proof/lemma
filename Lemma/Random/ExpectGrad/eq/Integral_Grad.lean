import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import sympy.stats.policy_trajectory
import sympy.vector.operators
open MeasureTheory PolicyGradient Random


/--
Path-binder Expect of `∇[θ] (V θ (s n))` equals the Bochner integral of the same observable.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ} {n : ℕ}
  {V : Θ → S → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
-- given
  [PSpace (M θ) (AsPathRV.path s)] :
-- imply
  𝔼[s : M θ](∇[θ] (V θ (s n))) =
    ∫ ω, ∇[θ] (V θ (s n ω)) ∂(M θ) := by
-- proof
  apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun path : ℕ → S ↦ ∇[θ] (V θ (path n)))
  apply (StronglyMeasurable.comp_measurable
    (f := fun x : S ↦ ∇[θ] (V θ x))
    StronglyMeasurable.of_discrete
    (measurable_pi_apply n)).aestronglyMeasurable


-- created on 2026-10-21
