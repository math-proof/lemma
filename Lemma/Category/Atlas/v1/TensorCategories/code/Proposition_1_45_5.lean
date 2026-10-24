import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_45_5
open FusionRing Matrix BigOperators


/--
[Proposition_1_45_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_45_5.lean)
-/
@[path]
private lemma Proposition_1_45_5_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {fpd : R.FPdimData}
  [Nonempty ι]
  [HasPerronFrobeniusProperty ι] :
-- imply
  (fpd.d R.unit = 1 ∧ (∀ i j, fpd.d i * fpd.d j = ∑ k : ι, (R.N i j k : ℝ) * fpd.d k)) ∧ ((∀ X, (R.leftMulMatrixR X).mulVec fpd.d = fpd.d X • fpd.d) ∧ (∀ i, fpd.d i > 0) ∧ (fpd.catDim > 0) ∧ (∀ j Y, ∑ k, (R.N j Y k : ℝ) * fpd.d k = fpd.d j * fpd.d Y) ∧ (∀ (w : ι → ℝ) (r : ℝ), (∀ i, 0 < w i) → R.rightMulMatrix.mulVec w = r • w → ∃ c : ℝ, ∀ i, w i = c * fpd.d i)) ∧ (∀ (χ : ι → ℝ), χ R.unit = 1 → (∀ i, 0 ≤ χ i) → (∀ i j, χ i * χ j = ∑ k : ι, (R.N i j k : ℝ) * χ k) → ∀ i, χ i = fpd.d i) ∧ (∀ X, (R.leftMulMatrixR X).mulVec fpd.d = fpd.d X • fpd.d) := by
-- proof
  apply FusionRing.Proposition_1_45_5 fpd


-- created on 2026-10-23
