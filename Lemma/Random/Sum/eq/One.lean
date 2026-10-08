import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
Total probability: summing the point density `Pr(x)` of a (discrete) random variable over
all values gives `1` — the law `π.map x` is a probability measure, and its density sums to
one against the counting reference measure.

Python: Random.Sum.eq.One (marked `provable=False` there; proved here in the discrete
countable setting where the reference measure on `α` is `count`).
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω}
  {x : Ω → α}
-- given
  (hP : SinglePSpace π x)
  (hμ : ReferenceMeasure.measure (α := α) = Measure.count) :
-- imply
  ∑' «x.bvar» : α, ℙ[π](x = «x.bvar») = 1 := by
-- proof
  obtain ⟨ρ, D, hρ⟩ := hP.exists_distribution
  have hρ' : π.map x = ReferenceMeasure.measure.withDensity ρ := hρ
  have hp : Measurable ρ := D.measurable_density
  have hD : π.map x = Measure.count.withDensity ρ := by
    rw [hρ', hμ]
  -- the canonical density is `ρ` a.e. w.r.t. the counting measure, hence everywhere
  have hae : π.prob x =ᵐ[Measure.count] ρ := by
    show (π.map x).rnDeriv ReferenceMeasure.measure =ᵐ[Measure.count] ρ
    rw [hD, hμ]
    exact Measure.rnDeriv_withDensity _ hp
  have hpt : ∀ a : α, π.prob x a = ρ a :=
    fun a => Measure.ae_count_iff.mp hae a
  -- the law `π.map x` has total mass `1`
  have hmass : ∑' a : α, ρ a = 1 := by
    rw [← lintegral_count ρ, ← setLIntegral_univ ρ,
      ← withDensity_apply ρ MeasurableSet.univ, ← hD,
      Measure.map_apply_of_aemeasurable hP.aemeasurable MeasurableSet.univ,
      Set.preimage_univ]
    exact hP.toPSpace.toIsProbabilityMeasure.measure_univ
  simp only [hpt]
  exact hmass


-- created on 2026-10-08
