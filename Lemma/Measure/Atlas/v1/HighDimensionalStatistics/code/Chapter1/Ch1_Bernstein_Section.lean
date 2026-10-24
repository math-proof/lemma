import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Lemma_1_8
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_16
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_8
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_16
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_11
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_19
open MeasureTheory Real Set Measure ProbabilityTheory


/--
[proposition_1_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Ch1_Bernstein_Section.lean)
-/
@[path]
lemma proposition_1_1
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  gaussianReal 0 1 (Ioi t) ≤ ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹ * t⁻¹ * Real.exp (-(t ^ 2 / 2))) :=
-- proof
  Rigollet.Chapter1.proposition_1_1_mills_prob_upper t ht
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/--
[theorem_1_13](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Ch1_Bernstein_Section.lean)
-/
@[path]
lemma theorem_1_13
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  {t lambda : ℝ}
-- given
  (hn : 0 < n)
  (ht : 0 < t)
  (hlam : 0 < lambda)
  (hIndep : iIndepFun X μ)
  (hMeas : ∀ i, Measurable (X i))
  (hSubExp : ∀ i, @IsSubExponential _ _ (μ := μ) _ (X i) lambda)
  (hInt : ∀ i (s : ℝ), |s| ≤ 1 / lambda → Integrable (fun ω => Real.exp (s * X i ω)) μ) :
-- imply
  max (μ.real {ω | t ≤ 1 / ↑n * ∑ i, X i ω}) (μ.real {ω | 1 / ↑n * ∑ i, X i ω ≤ -t}) ≤ Real.exp (-(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda))) :=
-- proof
  theorem_1_13_bernstein_inequality hn ht hlam hIndep hMeas hSubExp hInt

/--
[lemma_1_15_bounded_subgaussian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Ch1_Bernstein_Section.lean)
-/
@[path]
lemma lemma_1_15_bounded_subgaussian
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {a b : ℝ}
-- given
  (hab : a < b)
  (hMeas : Measurable X)
  (hInt : Integrable X μ)
  (ha : ∀ᵐ ω ∂μ, a ≤ X ω)
  (hb : ∀ᵐ ω ∂μ, X ω ≤ b)
  (hMean : ∫ ω, X ω ∂μ = 0) :
-- imply
  IsSubGaussian X ((b - a) ^ 2 / 4) μ :=
-- proof
  lemma_1_8_hoeffding hab hMeas hInt ha hb hMean

/--
[theorem_1_16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Ch1_Bernstein_Section.lean)
-/
@[path]
lemma theorem_1_16
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → E →ₗ[ℝ] ℝ}
  {S : Finset E}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => (g ω) v) σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | ∃ θ ∈ (convexHull ℝ) ↑S, (g ω) θ > t} ≤ S.card • ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * σsq)))) :=
-- proof
  theorem_1_16_polytope_subgaussian g S hsg t ht

/--
[def_1_17_epsilon_net_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Ch1_Bernstein_Section.lean)
-/
@[path]
lemma def_1_17_epsilon_net_exists
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [PseudoMetricSpace X]
  {K : Set X}
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  ∃ N, N ⊆ K ∧ (∀ x ∈ N, ∀ y ∈ N, x ≠ y → ε < dist x y) ∧ ∀ z ∈ K, ∃ x ∈ N, dist x z ≤ ε :=
-- proof
  exists_maximal_separated_net K ε hε

/--
[theorem_1_19_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Ch1_Bernstein_Section.lean)
-/
@[path]
lemma theorem_1_19_expectation
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {d : ℕ}
  {_ : MeasurableSpace Ω}
  {μ : Measure Ω}
  {_ : IsProbabilityMeasure μ}
  {X : Ω → EuclideanSpace ℝ (Fin d)}
  {σsq : ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σsq)
  (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 → IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ) :
-- imply
  ∫ ω, ‖X ω‖ ∂μ ≤ 4 * Real.sqrt σsq * Real.sqrt d :=
-- proof
  theorem_1_19_expectation_bound hd hσ hsg

/--
[theorem_1_19_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Ch1_Bernstein_Section.lean)
-/
@[path]
lemma theorem_1_19_tail
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → EuclideanSpace ℝ (Fin d)}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σsq)
  (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 → IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ 1 ∧ @inner ℝ _ _ θ (X ω) > t} ≤ ENNReal.ofReal ((6 : ℝ) ^ d * Real.exp (-(t ^ 2 / (8 * σsq)))) :=
-- proof
  theorem_1_19_tail_bound hd hσ hsg t ht

/--
[theorem_1_19_high_probability](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Ch1_Bernstein_Section.lean)
-/
@[path]
lemma theorem_1_19_high_probability
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {d : ℕ}
  {_ : MeasurableSpace Ω}
  {μ : Measure Ω}
  {_ : IsProbabilityMeasure μ}
  {X : Ω → EuclideanSpace ℝ (Fin d)}
  {σsq : ℝ}
  {δ : ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σsq)
  (hsg : ∀ (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 → IsSubGaussian (fun ω => @inner ℝ _ _ a (X ω)) σsq μ)
  (hδ_pos : 0 < δ)
  (hδ_lt : δ < 1) :
-- imply
  μ {ω | ‖X ω‖ > 4 * Real.sqrt σsq * Real.sqrt d + 2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ))} ≤ ENNReal.ofReal δ :=
-- proof
  theorem_1_19_high_prob hd hσ hsg hδ_pos hδ_lt


-- created on 2026-10-23
