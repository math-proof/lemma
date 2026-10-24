import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc2_covedgeascube
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc2_cubeIntegral_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covedgeascube.lean)
-/
@[path]
private lemma oc2_cubeIntegral_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = Lindeberg.mean μ g := by
-- proof
  apply StatMech.Walls.oc2_cubeIntegral_eq_mean μ hpos hμ1 σ g

/--
[oc2_cubeCov_eq_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covedgeascube.lean)
-/
@[path]
private lemma oc2_cubeCov_eq_cov_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {F G : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  oc2_cubeCov μ (σ : Fin n → E) F G = Lindeberg.cov μ F G := by
-- proof
  apply StatMech.Walls.oc2_cubeCov_eq_cov μ hpos hμ1 σ F G

/--
[oc2_cov_edge_as_cube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covedgeascube.lean)
-/
@[path]
private lemma oc2_cov_edge_as_cube_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  Lindeberg.cov μ f (Lindeberg.coord e) = oc2_cubeCov μ (σ : Fin n → E) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.Walls.oc2_cov_edge_as_cube μ hpos hμ1 σ f e

/--
[oc2_cov_edge_as_cube_coordI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covedgeascube.lean)
-/
@[path]
private lemma oc2_cov_edge_as_cube_coordI_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  Lindeberg.cov μ f (CovLowerBound.coordI e) = oc2_cubeCov μ (σ : Fin n → E) f (CovLowerBound.coordI e) := by
-- proof
  apply StatMech.Walls.oc2_cov_edge_as_cube_coordI μ hpos hμ1 σ f e


-- created on 2026-10-23
