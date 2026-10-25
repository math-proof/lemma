import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.DoobDecomposition
open MeasureTheory Filter DoobDecomposition
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory


namespace DoobDecomposition

/--
[predictablePart_mono_of_submartingale](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/DoobDecomposition.lean)
-/
@[path]
lemma predictablePart_mono_of_submartingale
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {n : ℕ}
-- given
  (hf : Submartingale f ℱ μ) :
-- imply
  predictablePart f ℱ μ n ≤ᵐ[μ] predictablePart f ℱ μ (n + 1) := by
-- proof
  have key : (0 : Ω → ℝ) ≤ᵐ[μ] μ[f (n + 1) - f n | ℱ n] :=
    hf.condExp_sub_nonneg (Nat.le_succ n)
  filter_upwards [key] with ω hω
  simp only [predictablePart, Finset.sum_apply, Finset.sum_range_succ, Pi.zero_apply] at hω ⊢
  linarith

end DoobDecomposition

namespace DoobDecomposition

/--
[doob_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/DoobDecomposition.lean)
-/
@[path]
lemma doob_decomposition
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [SigmaFiniteFiltration μ ℱ]
-- given
  (hf : Submartingale f ℱ μ) :
-- imply
  Martingale (martingalePart f ℱ μ) ℱ μ ∧ (predictablePart f ℱ μ 0 = 0) ∧ StronglyAdapted ℱ (fun n => predictablePart f ℱ μ (n + 1)) ∧ (∀ n, predictablePart f ℱ μ n ≤ᵐ[μ] predictablePart f ℱ μ (n + 1)) ∧ (martingalePart f ℱ μ + predictablePart f ℱ μ = f) :=
-- proof
  ⟨martingale_martingalePart hf.stronglyAdapted hf.integrable,
    predictablePart_zero,
    stronglyAdapted_predictablePart,
    fun n => predictablePart_mono_of_submartingale hf n,
    martingalePart_add_predictablePart ℱ μ f⟩

end DoobDecomposition


-- created on 2026-10-23
