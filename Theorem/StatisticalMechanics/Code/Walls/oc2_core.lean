/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc2_covedgeascube
import Theorem.StatisticalMechanics.Code.Walls.oc2_thetamatch.Part2
import Theorem.StatisticalMechanics.Code.Walls.oc2_codinglawsingle
import Theorem.StatisticalMechanics.Code.Walls.oc2_coordreadmatch
import Def.StatisticalMechanics.Code.Walls.oc2_core
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.Coding

open StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc2_corr_covSum_eq_cubeCovSum (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e))
      = oc2_cubeCovSum μ (σ : Fin n → E) f :=
  Finset.sum_congr rfl (fun e _ => oc2_cov_edge_as_cube_coordI μ hpos hμ1 σ f e)


theorem oc2_corr_mean_eq_cubeIntegral (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) :=
  (oc2_cubeIntegral_eq_mean μ hpos hμ1 σ f).symm


theorem oc2_codingCovBridge_cubeFrame (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e)) = oc2_cubeCovSum μ (σ : Fin n → E) f
      ∧ Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) :=
  ⟨oc2_corr_covSum_eq_cubeCovSum μ hpos hμ1 σ f,
   oc2_corr_mean_eq_cubeIntegral μ hpos hμ1 σ f⟩


end Walls
end StatMech
