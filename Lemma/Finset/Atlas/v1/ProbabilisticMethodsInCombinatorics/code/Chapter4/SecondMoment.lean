import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.SecondMoment
open MeasureTheory ProbabilityTheory Filter


namespace ProbabilityTheory

/--
[chebyshev_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/SecondMoment.lean)
-/
@[path]
lemma chebyshev_inequality
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {X : Ω → ℝ}
  {t : ℝ}
-- given
  (hX : MemLp X 2 μ)
  (ht : 0 < t) :
-- imply
  μ {ω | t ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / t ^ 2) :=
-- proof
  meas_ge_le_variance_div_sq hX ht

end ProbabilityTheory

namespace ProbabilityTheory

/--
[prob_eq_zero_le_variance_div_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/SecondMoment.lean)
-/
@[path]
lemma prob_eq_zero_le_variance_div_sq
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {X : Ω → ℝ}
-- given
  (hX : MemLp X 2 μ)
  (hE : 0 < ∫ ω, X ω ∂μ) :
-- imply
  μ {ω | X ω = 0} ≤ ENNReal.ofReal (Var[X; μ] / (∫ ω, X ω ∂μ) ^ 2) := by
-- proof
  have h_sub : {ω | X ω = 0} ⊆ {ω | (∫ ω, X ω ∂μ) ≤ |X ω - ∫ ω, X ω ∂μ|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω, zero_sub, abs_neg, abs_of_pos hE]
  calc μ {ω | X ω = 0}
    ≤ μ {ω | (∫ ω, X ω ∂μ) ≤ |X ω - ∫ ω, X ω ∂μ|} := measure_mono h_sub
    _ ≤ ENNReal.ofReal (Var[X; μ] / (∫ ω, X ω ∂μ) ^ 2) :=
      meas_ge_le_variance_div_sq hX hE

end ProbabilityTheory

namespace ProbabilityTheory

/--
[tendsto_prob_eq_zero_of_variance_div_sq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/SecondMoment.lean)
-/
@[path]
lemma tendsto_prob_eq_zero_of_variance_div_sq_tendsto
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {X : ℕ → Ω → ℝ}
-- given
  (hX : ∀ n, MemLp (X n) 2 μ)
  (hE : ∀ n, 0 < ∫ ω, X n ω ∂μ)
  (hVar : Tendsto (fun n => Var[X n; μ] / (∫ ω, X n ω ∂μ) ^ 2) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => μ {ω | X n ω = 0}) atTop (nhds 0) := by
-- proof
  have hup : Tendsto (fun n => ENNReal.ofReal (Var[X n; μ] / (∫ ω, X n ω ∂μ) ^ 2)) atTop (nhds 0) := by
    have h := ENNReal.tendsto_ofReal hVar
    rwa [ENNReal.ofReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => zero_le _) (fun n => prob_eq_zero_le_variance_div_sq (hX n) (hE n))

end ProbabilityTheory

namespace ProbabilityTheory

/--
[second_moment_method](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/SecondMoment.lean)
-/
@[path]
lemma second_moment_method
  {Ω : ℕ → Type*}
  [∀ n, MeasurableSpace (Ω n)]
  {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)]
  {X : ∀ n, Ω n → ℝ}
-- given
  (hX : ∀ n, MemLp (X n) 2 (μ n))
  (hμ_pos : ∀ n, 0 < (μ n)[X n])
  (hVar : Tendsto (fun n => Var[X n ; μ n] / (μ n)[X n] ^ 2) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => (μ n) {ω | X n ω = 0}) atTop (𝓝 0) := by
-- proof
  have h_upper_tends : Tendsto (fun n => ENNReal.ofReal (Var[X n ; μ n] / (μ n)[X n] ^ 2))
    atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hVar
    rwa [ENNReal.ofReal_zero] at this
  have h_bound : ∀ n, (μ n) {ω | X n ω = 0} ≤
    ENNReal.ofReal (Var[X n ; μ n] / (μ n)[X n] ^ 2) :=
    fun n => prob_eq_zero_le_variance_div_sq (hX n) (hμ_pos n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper_tends
    (fun n => zero_le _) h_bound

end ProbabilityTheory


-- created on 2026-10-23
