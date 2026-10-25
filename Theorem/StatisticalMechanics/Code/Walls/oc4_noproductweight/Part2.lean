/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc2_thetamatch.Part2
import Theorem.StatisticalMechanics.Code.Walls.oc3_noproductweight.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc3_core
import Def.StatisticalMechanics.Code.Walls.oc4_noproductweight
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

open StatMech.OSSS.CovLowerBound

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc4_posCorrMu_pos : ∀ ω, 0 < oc4_posCorrMu ω := by
  intro ω; unfold oc4_posCorrMu; split <;> norm_num


theorem oc4_posCorrMu_sum_eq_one : ∑ ω : ConfigSpace (Fin 2), oc4_posCorrMu ω = 1 := by
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [huniv]
  unfold oc4_posCorrMu
  norm_num [Finset.sum_insert, Finset.mem_insert, Matrix.cons_val_zero, Matrix.cons_val_one]


theorem oc4_posCorrMu_cov_ne_zero :
    Lindeberg.cov oc4_posCorrMu (Lindeberg.coord (0 : Fin 2)) (Lindeberg.coord (1 : Fin 2)) ≠ 0 := by
  unfold Lindeberg.cov Lindeberg.mean Lindeberg.coord oc4_posCorrMu
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [huniv]
  norm_num [Finset.sum_insert, Finset.mem_insert, Matrix.cons_val_zero, Matrix.cons_val_one]


theorem oc4_posCorrMu_genuinelyCorrelated : oc3_GenuinelyCorrelated oc4_posCorrMu :=
  ⟨0, 1, by decide, oc4_posCorrMu_cov_ne_zero⟩


theorem oc4_no_product_weight_expectAsCubeAt_witness (σ : Fin 2 ≃ Fin 2) :
    ¬ ∃ ν : Fin 2 → Bool → ℝ, IsProbWeight ν ∧
        ∀ f, oc2_ExpectAsCubeAt ν oc4_posCorrMu (σ : Fin 2 → Fin 2) f :=
  oc4_no_product_weight_expectAsCubeAt oc4_posCorrMu oc4_posCorrMu_pos
    oc4_posCorrMu_sum_eq_one σ oc4_posCorrMu_genuinelyCorrelated

end Walls
end StatMech
