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
import Def.StatisticalMechanics.Code.Walls.oc2_thetamatch.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc2_thetaMatch_holds (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ)
    (f : ConfigSpace E → ℝ)
    (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    oc2_ThetaMatch μ ν f (Lindeberg.mean μ f) :=
  ⟨rfl, oc2_theta_match μ hpos hμ1 σ ν f hcube⟩


theorem oc2_theta_match_bridge_clause (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ)
    (f : ConfigSpace E → ℝ)
    (hcube : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    Lindeberg.mean μ f = expect ν f :=
  oc2_theta_match μ hpos hμ1 σ ν f hcube


theorem oc2_expect_empty [IsEmpty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    expect ν g = g ω := by
  unfold OSSS.expect OSSS.weight
  rw [Finset.sum_eq_single ω]
  · rw [Finset.prod_of_isEmpty]; ring
  · intro b _ hb; exact absurd (Subsingleton.elim b _) hb
  · intro h; exact absurd (Finset.mem_univ _) h


theorem oc2_expectAsCubeAt_empty [IsEmpty E] (μ : ConfigSpace E → ℝ) (ν : E → Bool → ℝ)
    (σ : Fin 0 ≃ E) (f : ConfigSpace E → ℝ) :
    oc2_ExpectAsCubeAt ν μ (σ : Fin 0 → E) f := by
  unfold oc2_ExpectAsCubeAt
  have hconst : (fun u => f (codeMap μ (σ : Fin 0 → E) u))
      = (fun _ => f (codeMap μ (σ : Fin 0 → E) (fun _ => 0))) := by
    funext u; congr 1
  rw [hconst, integral_const, probReal_univ, one_smul]
  exact oc2_expect_empty ν f _


theorem oc2_theta_match_empty [IsEmpty E] (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (σ : Fin 0 ≃ E) (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ) :
    Lindeberg.mean μ f = expect ν f :=
  oc2_theta_match μ hpos hμ1 σ ν f (oc2_expectAsCubeAt_empty μ ν σ f)

end Walls
end StatMech
