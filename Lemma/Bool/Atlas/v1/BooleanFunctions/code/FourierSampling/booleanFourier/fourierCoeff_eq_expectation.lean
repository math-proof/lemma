import Mathlib
import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
open BooleanFourier Bool


/--
[fourierCoeff_eq_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierSampling.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {S : Finset (Fin n)} :
-- imply
  fourierCoeff f S = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, f x * chi S x := by
-- proof
  rfl


lemma BooleanFourier.fourierCoeff_eq_expectation
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {S : Finset (Fin n)} :
-- imply
  fourierCoeff f S = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, f x * chi S x := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
