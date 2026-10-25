/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc2_whynotperedge
import Def.StatisticalMechanics.Code.Walls.oc3_noproductweight.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.CovLowerBound

open StatMech.OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc3_corrMu_sum_eq_one : ∑ ω : ConfigSpace (Fin 2), oc3_corrMu ω = 1 := by
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [huniv]
  unfold oc3_corrMu
  norm_num [Finset.sum_insert, Finset.mem_insert, Matrix.cons_val_zero, Matrix.cons_val_one]


theorem oc3_corrMu_nonneg : ∀ ω, 0 ≤ oc3_corrMu ω := by
  intro ω; unfold oc3_corrMu; split <;> norm_num


theorem oc3_corrMu_cov_ne_zero :
    Lindeberg.cov oc3_corrMu (Lindeberg.coord (0 : Fin 2)) (Lindeberg.coord (1 : Fin 2)) ≠ 0 := by
  unfold Lindeberg.cov Lindeberg.mean Lindeberg.coord oc3_corrMu
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [huniv]
  norm_num [Finset.sum_insert, Finset.mem_insert, Matrix.cons_val_zero, Matrix.cons_val_one]


theorem oc3_corrMu_genuinelyCorrelated : oc3_GenuinelyCorrelated oc3_corrMu :=
  ⟨0, 1, by decide, oc3_corrMu_cov_ne_zero⟩


theorem oc3_no_product_weight_witness :
    ¬ ∃ ν : Fin 2 → Bool → ℝ, IsProbWeight ν ∧
        ∀ g, expect ν g = Lindeberg.mean oc3_corrMu g :=
  oc3_no_product_weight oc3_corrMu_genuinelyCorrelated


section FK

open StatMech.OSSS.MonotonicFK


theorem oc3_fk_no_product_weight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℝ) (e e' : Sym2 V) (he : e ≠ e')
    (hcorr : Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') ≠ 0) :
    ¬ ∃ ν : Sym2 V → Bool → ℝ, IsProbWeight ν ∧
        ∀ g, expect ν g = Lindeberg.mean (fkMass G p q) g :=
  oc3_no_product_weight ⟨e, e', he, hcorr⟩

end FK
end Walls
end StatMech
