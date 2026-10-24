import Mathlib
import sympy.Basic
open MeasureTheory ProbabilityTheory Filter Finset Topology


namespace StrongLaw

/--
[strong_law_of_large_numbers_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongLaw.lean)
-/
@[path]
lemma strong_law_of_large_numbers_real
  {m : MeasurableSpace Ω}
  {μ : MeasureTheory.Measure Ω}
  {X : ℕ → Ω → ℝ}
-- given
  (hint : Integrable (X 0) μ)
  (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
  (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
-- imply
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, X i ω) / (n : ℝ)) atTop (𝓝 (∫ x, X 0 x ∂μ)) := by
-- proof
  have h := ProbabilityTheory.strong_law_ae X hint hindep hident
  filter_upwards [h] with ω hω
  simp only [smul_eq_mul] at hω
  exact hω.congr (fun n => by ring)

end StrongLaw

namespace StrongLaw

/--
[textbook_strong_law_ae](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongLaw.lean)
-/
@[path]
lemma textbook_strong_law_ae
  {m : MeasurableSpace Ω}
  {μ : MeasureTheory.Measure Ω}
  {X : ℕ → Ω → ℝ}
-- given
  (hint : Integrable (X 0) μ)
  (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
  (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
-- imply
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, X i ω) / (n : ℝ)) atTop (𝓝 (∫ x, X 0 x ∂μ)) :=
-- proof
  strong_law_of_large_numbers_real X hint hindep hident

end StrongLaw


-- created on 2026-10-23
