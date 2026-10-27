import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.FubiniTheorem
open MeasureTheory MeasurableSpace Measure ENNReal


/--
[fubini_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/FubiniTheorem.lean)
-/
@[path]
lemma fubini_theorem
  [MeasurableSpace α]
  [MeasurableSpace β]
  {μ : Measure α}
  {ν : Measure β}
  [SFinite μ]
  [SFinite ν]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {f : α × β → E}
-- given
  (hf : Integrable f (μ.prod ν)) :
-- imply
  ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ ∧ ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν ∧ ∫ x, ∫ y, f (x, y) ∂ν ∂μ = ∫ y, ∫ x, f (x, y) ∂μ ∂ν :=
-- proof
  ⟨integral_prod f hf, integral_prod_symm f hf,
    (integral_prod f hf).symm.trans (integral_prod_symm f hf)⟩


-- created on 2026-10-23
