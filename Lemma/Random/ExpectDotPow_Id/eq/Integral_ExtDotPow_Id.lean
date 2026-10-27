import Theorem.Dynamics.PolicyTrajectory
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
open MeasureTheory PolicyGradient PolicyGradient.Model


/--
Discounted return under the path binder: `𝔼[r: M θ]((γ ^ id) @ r)` is the Bochner integral of the same observable.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ} {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
-- given
  [PSpace (M θ) (AsPathRV.path r)] :
-- imply
  𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ) := by
-- proof
  apply Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun path : ℕ → ℝ ↦ ((γ ^ (id : ℕ → ℕ)) @ path))
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t ↦
    (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable


-- created on 2026-10-17
