/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.Walls.oc2_codinglawsingle
import Def.StatisticalMechanics.Code.Walls.oc2_thetamatch
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc2_theta_match (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ)
    (f : ConfigSpace E → ℝ)
    (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    Lindeberg.mean μ f = expect ν f := by
  rw [hcube, oc2_coding_law_single μ hpos hμ1 σ f]
  rfl


theorem oc2_theta_match_triple (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ)
    (f : ConfigSpace E → ℝ)
    (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)
      ∧ (∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)) = expect ν f := by
  refine ⟨?_, hcube.symm⟩
  rw [oc2_coding_law_single μ hpos hμ1 σ f]
  rfl


theorem oc2_theta_match_sum (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ)
    (f : ConfigSpace E → ℝ)
    (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    (∑ x, f x * μ x) = expect ν f := by
  have h := oc2_theta_match μ hpos hμ1 σ ν f hcube
  rwa [Lindeberg.mean] at h


end Walls
end StatMech
