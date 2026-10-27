import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part3
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
open MeasureTheory PolicyGradient PolicyGradient.DensityModel Random Measure


/--
Discounted return under the continuous-action path binder:
`𝔼[r: M θ]((γ ^ id) @ r)` is the ContinuousAndEq_1AndAll_EqIm0AndGeRe0.is.Any_And_All_Eq_CharFun integral of the same observable.
Continuous-action counterpart of `Random.ExpectDotPow_Id.eq.Integral_ExtDotPow_Id`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A} {θ : Θ} {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
-- given
  [PSpace (M θ) (AsPathRV.path r)] :
-- imply
  𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ) := by
-- proof
  apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun path : ℕ → ℝ ↦ ((γ ^ (id : ℕ → ℕ)) @ path))
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t ↦
    (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable


-- created on 2026-10-20
