import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.NoisyHypercube.booleanFourier.correlatedProb_factor_nonneg
open Finset BigOperators BooleanFourier Bool


/--
[correlatedProb_factor_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoisyHypercube.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {ρ : ℝ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  ∑ b : Bool, (1 + ρ * (boolToReal (x i) * boolToReal b)) / 2 = 1 := by
-- proof
  simp only [Fintype.sum_bool]
  cases x i <;> simp [boolToReal] <;> ring


lemma BooleanFourier.correlatedProb_factor_sum
  {n : ℕ}
  {ρ : ℝ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  ∑ b : Bool, (1 + ρ * (boolToReal (x i) * boolToReal b)) / 2 = 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
