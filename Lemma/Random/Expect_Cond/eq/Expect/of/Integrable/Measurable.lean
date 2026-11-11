import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorem.Probability.CondExpectation
open MeasureTheory ProbabilityTheory


/--
Law of total expectation, also called the law of iterated expectations, for a
random variable `X` with countably many values:
`𝔼[𝔼[Y | X]] = 𝔼[Y]`. The inner expectation is `𝔼[Y | X = «\sf{X}»]`, and the outer one
sums those values against `ℙ(X = «\sf{X}»)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  {π : Measure Ω} {X : Ω → α} [PSpace π X]
  {Y : Ω → ℝ} [PSpace π Y]
-- given
  (hX : Measurable X)
  (hY : Integrable Y π) :
-- imply
  𝔼[X: π](𝔼[Y: π](Y | X)) = 𝔼[Y: π](Y) := by
-- proof
  change Expectation.ofRV π X (fun x => Expectation.condEvent π Y X (fun a => a) x) =
    Expectation.ofRV π Y (fun a => a)
  simp only [Expectation.ofRV, Expectation.condEvent, expectation_real]
  have hcond (x : α) : ∫ a, a ∂(π[|X ⁻¹' {x}].map Y) =
    ∫ ω, Y ω ∂π[|X ⁻¹' {x}] := by
    rw [← expectation_real, ← Expectation.condEvent]
    apply Expectation.condEvent_eq_integral
    · apply PSpace.aemeasurable (x := Y)
    · apply measurable_id
  simp_rw [hcond]
  have hscale (x : α) (f : Ω → ℝ) :
    (π (X ⁻¹' {x})).toReal * ∫ ω, f ω ∂π[|X ⁻¹' {x}] =
      ∫ ω in X ⁻¹' {x}, f ω ∂π := by
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ← mul_assoc, ENNReal.toReal_inv]
    if hx : π (X ⁻¹' {x}) = 0 then
      rw [Measure.restrict_eq_zero.mpr hx]
      simp
    else
      rw [mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hx, measure_ne_top π _⟩), one_mul]
  have hdisj : Pairwise (fun x y => Disjoint (X ⁻¹' {x}) (X ⁻¹' {y})) :=
    fun x y hxy => Set.disjoint_left.mpr fun ω h₃ h₄ => hxy (h₃.symm.trans h₄)
  have hnorm (x : α) :
    (π (X ⁻¹' {x})).toReal * ‖∫ ω, Y ω ∂π[|X ⁻¹' {x}]‖ ≤
      ∫ ω in X ⁻¹' {x}, ‖Y ω‖ ∂π := calc
    _ ≤ (π (X ⁻¹' {x})).toReal * ∫ ω, ‖Y ω‖ ∂π[|X ⁻¹' {x}] :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) ENNReal.toReal_nonneg
    _ = ∫ ω in X ⁻¹' {x}, ‖Y ω‖ ∂π := hscale x _
  have hint : Integrable (fun x => ∫ ω, Y ω ∂π[|X ⁻¹' {x}]) (π.map X) := by
    rw [Measure.map_eq_sum π X hX]
    apply integrable_sum_dirac (fun x => measure_ne_top π _)
    apply Summable.of_nonneg_of_le (fun x => mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)) hnorm
    apply HasSum.summable
    apply hasSum_integral_iUnion (fun x => hX (measurableSet_singleton x)) hdisj
    apply hY.norm.integrableOn
  rw [integral_countable hint]
  simp_rw [map_measureReal_apply hX (measurableSet_singleton _), measureReal_def, smul_eq_mul, hscale]
  have hmap : ∫ a, a ∂(π.map Y) = ∫ ω, Y ω ∂π := by
    apply integral_map
    · apply PSpace.aemeasurable (x := Y)
    · apply measurable_id.aestronglyMeasurable
  rw [hmap]
  rw [← integral_iUnion (fun x => hX (measurableSet_singleton x)) hdisj hY.integrableOn]
  have hunion : (⋃ x, X ⁻¹' {x}) = Set.univ := by
    ext ω
    simp
  rw [hunion, Measure.restrict_univ]


-- created on 2023-03-31
-- updated on 2026-11-11
