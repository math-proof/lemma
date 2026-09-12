import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
Discrete law of the unconscious statistician: when `x : Ω → α` takes values in a countable
space (measurable singletons), the expectation of `f(x)` is the sum of each value `f a`
weighted by the probability that `x = a`.

  `𝔼[f(x)] = ∑' a, f a · Pr(x = a)`

This is the discrete counterpart of integrating against a density; the probability mass
`Pr(x = a)` is the singleton mass of the pushforward law `𝕡.map x`.
-/
@[main]
private lemma main
  {Ω α : Type*}
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  [Countable α]
  [MeasurableSingletonClass α]
  (𝕡 : Measure Ω)
  (x : Ω → α)
  (f : α → ENNReal)
-- given
  (hx : Measurable x)
  (hf : Measurable f) :
-- imply
  lintegral 𝕡 (fun ω ↦ f (x ω)) = ∑' a : α, f a * 𝕡.map x {a} := by
-- proof
  rw [← lintegral_map hf hx]
  exact lintegral_countable' f


/--
Conditional counterpart of the discrete expectation formula: conditioned on `y = b`, the
expectation of `f(x)` — the lintegral of `f` against the conditional law, i.e. the state
measure with density `JointPSpace.condDensity 𝕡 x y · b` — is the sum of each `f a`
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
  (hP : JointPSpace 𝕡 x y)
  (hf : Measurable f)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count)
  (b : β) :
-- imply
  lintegral (ReferenceMeasure.measure.withDensity (fun a ↦ JointPSpace.condDensity 𝕡 x y (a, b))) f
    = ∑' a : α, f a * JointPSpace.condDensity 𝕡 x y (a, b) := by
-- proof
  have hcd : Measurable (fun a : α ↦ JointPSpace.condDensity 𝕡 x y (a, b)) := by
    unfold JointPSpace.condDensity
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hcd hf, hμ, lintegral_count]
  exact tsum_congr fun _ ↦ mul_comm _ _


-- created on 2023-03-20
