import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc2_thetamatch.Part2
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc2_theta_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean)
-/
@[path]
private lemma oc2_theta_match_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
-- imply
  Lindeberg.mean μ f = expect ν f := by
-- proof
  apply StatMech.Walls.oc2_theta_match μ hpos hμ1 σ ν f hcube

/--
[oc2_theta_match_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean)
-/
@[path]
private lemma oc2_theta_match_triple_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
-- imply
  Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) ∧ (∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)) = expect ν f := by
-- proof
  apply StatMech.Walls.oc2_theta_match_triple μ hpos hμ1 σ ν f hcube

/--
[oc2_theta_match_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean)
-/
@[path]
private lemma oc2_theta_match_sum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
-- imply
  (∑ x, f x * μ x) = expect ν f := by
-- proof
  apply StatMech.Walls.oc2_theta_match_sum μ hpos hμ1 σ ν f hcube

/--
[oc2_thetaMatch_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean)
-/
@[path]
private lemma oc2_thetaMatch_holds_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
-- imply
  oc2_ThetaMatch μ ν f (Lindeberg.mean μ f) := by
-- proof
  apply StatMech.Walls.oc2_thetaMatch_holds μ hpos hμ1 σ ν f hcube

/--
[oc2_theta_match_bridge_clause](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean)
-/
@[path]
private lemma oc2_theta_match_bridge_clause_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
-- imply
  Lindeberg.mean μ f = expect ν f := by
-- proof
  apply StatMech.Walls.oc2_theta_match_bridge_clause μ hpos hμ1 σ ν f hcube

/--
[oc2_expect_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean)
-/
@[path]
private lemma oc2_expect_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  expect ν g = g ω := by
-- proof
  apply StatMech.Walls.oc2_expect_empty ν g ω

/--
[oc2_expectAsCubeAt_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean)
-/
@[path]
private lemma oc2_expectAsCubeAt_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {μ : ConfigSpace E → ℝ}
  {ν : E → Bool → ℝ}
  {σ : Fin 0 ≃ E}
  {f : ConfigSpace E → ℝ} :
-- imply
  oc2_ExpectAsCubeAt ν μ (σ : Fin 0 → E) f := by
-- proof
  apply StatMech.Walls.oc2_expectAsCubeAt_empty μ ν σ f

/--
[oc2_theta_match_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean)
-/
@[path]
private lemma oc2_theta_match_empty_eq
  [Fintype E]
  [DecidableEq E]
  [IsEmpty E]
  {μ : ConfigSpace E → ℝ}
  {σ : Fin 0 ≃ E}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  Lindeberg.mean μ f = expect ν f := by
-- proof
  apply StatMech.Walls.oc2_theta_match_empty μ hpos hμ1 σ ν f


-- created on 2026-10-23
