module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Parseval.booleanFourier.parseval
open Finset BigOperators BooleanFourier Bool


public section

/--
[claim_2_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Parseval.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {f g : (Fin n → Bool) → ℝ} :
-- imply
  (∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, f x * g x) ∧ (∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, f x ^ 2) :=
-- proof
  ⟨plancherel (f := f) (g := g), parseval (f := f)⟩


theorem BooleanFourier.claim_2_2
  {n : ℕ}
  {f g : (Fin n → Bool) → ℝ} :
-- imply
  (∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, f x * g x) ∧ (∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, f x ^ 2) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
