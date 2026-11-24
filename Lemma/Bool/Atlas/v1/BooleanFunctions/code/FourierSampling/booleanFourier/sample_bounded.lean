import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierSampling.booleanFourier.abs_chi_eq_one
open BooleanFourier Bool


/--
[sample_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierSampling.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool}
-- given
  (hf : ∀ x, |f x| ≤ 1) :
-- imply
  |f x * chi S x| ≤ 1 := by
-- proof
  rw [abs_mul, abs_chi_eq_one (S := S) (x := x), mul_one]
  exact hf x


lemma BooleanFourier.sample_bounded
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool}
-- given
  (hf : ∀ x, |f x| ≤ 1) :
-- imply
  |f x * chi S x| ≤ 1 :=
-- proof
  main hf


-- created on 2026-10-23
-- updated on 2026-11-24
