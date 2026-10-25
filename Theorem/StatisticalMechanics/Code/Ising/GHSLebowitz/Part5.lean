/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part4
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsL_split_sum_product (q : ConfigSpace V)
    (f : ((v : {v : V // q v = true}) → Bool) → ℝ)
    (g : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ) :
    (∑ a : ConfigSpace V, f (ghsLSplitEquiv q a).1 * g (ghsLSplitEquiv q a).2) =
      (∑ st, f st) * ∑ su, g su := by
  let T := (v : {v : V // q v = true}) → Bool
  let U := (v : {v : V // ¬ q v = true}) → Bool
  calc
    (∑ a : ConfigSpace V, f (ghsLSplitEquiv q a).1 * g (ghsLSplitEquiv q a).2) =
        ∑ p : T × U, f p.1 * g p.2 :=
      Equiv.sum_comp (ghsLSplitEquiv q) (fun p : T × U => f p.1 * g p.2)
    _ = (∑ st, f st) * ∑ su, g su := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro st _
      rw [Finset.mul_sum]


theorem ghsL_split_cross_product (q : ConfigSpace V)
    (f₀ f₁ : ((v : {v : V // q v = true}) → Bool) → ℝ)
    (g₀ g₁ : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ) :
    (∑ a : ConfigSpace V,
        f₀ (ghsLSplitEquiv q a).1 * g₀ (ghsLSplitEquiv q a).2) *
      (∑ a : ConfigSpace V,
        f₁ (ghsLSplitEquiv q a).1 * g₁ (ghsLSplitEquiv q a).2) =
    (∑ a : ConfigSpace V,
        f₀ (ghsLSplitEquiv q a).1 * g₁ (ghsLSplitEquiv q a).2) *
      (∑ a : ConfigSpace V,
        f₁ (ghsLSplitEquiv q a).1 * g₀ (ghsLSplitEquiv q a).2) := by
  simp_rw [ghsL_split_sum_product]
  ring


end Ising
end StatMech
