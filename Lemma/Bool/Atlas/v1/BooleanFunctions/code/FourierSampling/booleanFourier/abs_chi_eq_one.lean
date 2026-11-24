import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierSampling.booleanFourier.fourierCoeff_eq_expectation
open BooleanFourier Bool


/--
[abs_chi_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierSampling.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  |chi S x| = 1 := by
-- proof
  have h := chi_sq (S := S) (x := x)
  have hne := chi_ne_zero (S := S) (x := x)
  have habs_sq : |chi S x| ^ 2 = 1 := by
    rwa [sq_abs]
  have habs_nn : (0 : ℝ) ≤ |chi S x| := abs_nonneg _
  nlinarith [sq_nonneg (|chi S x| - 1)]


lemma BooleanFourier.abs_chi_eq_one
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  |chi S x| = 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
