import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Integral.CarlemanStieltjesCriterion
open Filter MeasureTheory Set
open scoped BigOperators Topology
open MetaMathlibExt


/--
[summable_geometric_means](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/CarlemanStieltjesCriterion.lean)
-/
@[path]
private lemma summable_geometric_means_eq
  {a : ℕ → ℝ}
-- given
  (ha : ∀ n, 0 ≤ a n)
  (hasum : Summable a) :
-- imply
  Summable (fun n =>
    (∏ k ∈ Finset.range (n + 1), a k) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) := by
-- proof
  apply MetaMathlibExt.summable_geometric_means ha hasum

/--
[carleman_stieltjes_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/CarlemanStieltjesCriterion.lean)
-/
@[path]
private lemma carleman_stieltjes_criterion_eq
  {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure μ]
-- given
  (hsupp : μ (Set.Iio (0 : ℝ)) = 0)
  (hint : ∀ k : ℕ, 0 < k → MeasureTheory.Integrable (fun x : ℝ => |x| ^ k) μ)
  (hcarleman : tsum (fun n : ℕ => ENNReal.rpow (ENNReal.ofReal (ProbabilityTheory.moment (id : ℝ → ℝ) (n + 1) μ)) (-1 / (2 * ((n + 1 : ℕ) : ℝ)))) = ⊤) :
-- imply
  StieltjesMomentDeterminate μ := by
-- proof
  apply MetaMathlibExt.carleman_stieltjes_criterion μ hsupp hint hcarleman


-- created on 2026-10-20
