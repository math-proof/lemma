import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.NoisyHypercube.Part2
open Finset BigOperators BooleanFourier


/--
[correlatedProb_factor_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoisyHypercube.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {ρ : ℝ}
  {x y : Fin n → Bool}
  {i : Fin n}
-- given
  (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
-- imply
  0 ≤ (1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2 := by
-- proof
  have hρ0 : (-1 : ℝ) ≤ ρ := hρ.1
  have hρ1 : ρ ≤ 1 := hρ.2
  cases x i <;> cases y i <;> simp [boolToReal] <;> linarith


lemma BooleanFourier.correlatedProb_factor_nonneg
  {n : ℕ}
  {ρ : ℝ}
  {x y : Fin n → Bool}
  {i : Fin n}
-- given
  (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
-- imply
  0 ≤ (1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2 :=
-- proof
  main hρ


-- created on 2026-10-23
-- updated on 2026-11-24
