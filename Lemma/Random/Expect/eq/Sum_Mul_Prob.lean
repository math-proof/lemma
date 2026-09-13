import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
Discrete law of the unconscious statistician: the expectation of `f(x)` under the law of
`x` — the pushforward `𝕡.map x`, whatever it is — is the sum of each value `f a` weighted
by the probability that `x = a`.

  `𝔼(f(x)) = ∑' a, f a · Pr(x = a)`

The probability mass `Pr(x = a)` is the singleton mass of the pushforward law `𝕡.map x`.
No measurability of `x` is required for the identity to hold (if `x` is not a.e.
measurable then `𝕡.map x` is the zero measure by definition of `Measure.map`, and both
sides vanish); a.e. measurability is what makes `𝕡.map x` the genuine law of `x`.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  [Countable α]
  [MeasurableSingletonClass α]
  {𝕡 : Measure Ω}
  {x : Ω → α}
  {f : α → ENNReal} :
-- imply
  Expectation (𝕡.map x) f = ∑' a : α, f a * 𝕡.map x {a} := by
-- proof
  simp only [Expectation]
  exact lintegral_countable' f


/--
Conditional counterpart of the discrete expectation formula: conditioned on `y = b`, the
expectation of `f(x)` — the integral of `f` against the conditional law, i.e. the state
measure with density `𝕡.condProb (x, y) · b` — is the sum of each `f a`
weighted by the conditional probability `Pr(x = a | y = b)`.

  `𝔼[f(x) | y = b] = ∑' a, f a · Pr(x = a | y = b)`

The state measure on `α` must be counting measure (`hμ`), which is the discrete case of
integrating against the conditional density.
-/
private lemma given
  {Ω α β : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α]
  [MeasurableSingletonClass α]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
  {f : α → ENNReal}
-- given
  (hP : PSpace 𝕡 (x, y))
  (hf : Measurable f)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count)
  (b : β) :
-- imply
  Expectation (ReferenceMeasure.measure.withDensity (fun a ↦ 𝕡.condProb (x, y) (a, b))) f = ∑' a : α, f a * 𝕡.condProb (x, y) (a, b) := by
-- proof
  simp only [Expectation]
  have hcd : Measurable (fun a : α ↦ 𝕡.condProb (x, y) (a, b)) := by
    unfold Measure.condProb
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hcd hf, hμ, lintegral_count]
  exact tsum_congr fun _ ↦ mul_comm _ _


-- created on 2023-03-20
-- updated on 2026-09-13
