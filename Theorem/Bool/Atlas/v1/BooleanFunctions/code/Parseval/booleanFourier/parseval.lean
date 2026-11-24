module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Parseval.booleanFourier.plancherel
open Finset BigOperators BooleanFourier Bool


public section

/--
[parseval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Parseval.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, f x ^ 2 := by
-- proof
  have h := plancherel (f := f) (g := f)
  simp only [innerProduct] at h
  rw [show ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff f S =
    ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 from
    Finset.sum_congr rfl (fun S _ => by ring)] at h
  rw [h]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => by ring)


theorem BooleanFourier.parseval
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, f x ^ 2 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
