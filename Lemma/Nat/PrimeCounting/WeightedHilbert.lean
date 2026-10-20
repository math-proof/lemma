import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.WeightedHilbert
open Set MeasureTheory
open scoped ComplexConjugate Matrix.Norms.L2Operator
open Matrix
open MathlibExt.NumberTheory.PrimeCounting


/--
[weightedHilbertCosecant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/WeightedHilbert.lean)
-/
@[path]
private lemma weightedHilbertCosecant_eq
  [Fintype ι] [DecidableEq ι]
  {x δ : ι → ℝ}
  {z : ι → ℂ}
-- given
  (hδ : ∀ r, 0 < δ r)
  (hsep : ∀ r s, r ≠ s → δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖) :
-- imply
  ‖∑ r, ∑ s ∈ Finset.univ.erase r,
    z r * conj (z s) / Real.sin (Real.pi * (x r - x s))‖ ≤
    3 / 2 * ∑ r, ‖z r‖ ^ 2 / δ r := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.weightedHilbertCosecant x δ z hδ hsep


-- created on 2026-10-20
