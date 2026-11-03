import Lemma.Random.NormWkd.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
`V0` is defined as the discounted `Wkd` series on every state:
`V0 θ γ x = ∑' k, γ ^ k * Wkd θ k x`.
(Hypothesis `_hP` is unused and kept only for path/API compatibility with older callers.)
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
-- given
  (_h : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S)
  (_hP : (M θ).real ((fun ω : ℕ → ℝ × S × A => (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  M.V0 θ γ x = ∑' k, γ ^ k * M.Wkd θ k x := rfl


-- created on 2026-10-07
-- updated on 2026-11-03
