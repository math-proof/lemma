import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import sympy.Basic

open MeasureTheory


/--
Contrapositive of `Random.EqPr__0.of.EqPr_0`: at a fixed value `x'` of the random
variable `x`, if the section of the joint density `y' ↦ 𝕡(x, y)(x', y')` is nonzero on a
non-negligible set of `y'` values, then its integral — the marginal density of `x` at `x'`
— is nonzero. With the counting measure as the reference measure, `∃ᵐ` reduces to the
existence of a single `y'` with `𝕡(x, y)(x', y') ≠ 0` and the `lintegral` to a sum,
recovering the discrete statement `𝕡(x, y) ≠ 0 ⟹ 𝕡(x) ≠ 0`.
-/
@[main]
private lemma main
  {Ω α β : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hp : JointPSpace 𝕡 x y)
  (x' : α)
  (h : ∃ᵐ y' ∂ReferenceMeasure.measure,
      JointPSpace.density 𝕡 x y (x', y') ≠ 0) :
-- imply
  ∫⁻ y', JointPSpace.density 𝕡 x y (x', y') ∂ReferenceMeasure.measure ≠ 0 := by
-- proof
  exact (lintegral_eq_zero_iff
    ((Measure.measurable_rnDeriv _ _).comp (measurable_const.prodMk measurable_id))).not.mpr
    fun h0 => h (h0.mono fun _ hy hne => hne hy)


-- created on 2020-12-12
-- updated on 2026-09-12
