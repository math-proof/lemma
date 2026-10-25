/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Instance.StatisticalMechanics.Code.Foundations.StrassenFull
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Transport

open Filter Topology


variable {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]


variable [DecidableRel ((· ≤ ·) : P → P → Prop)]


def pmargL : (OrderPairs P → ℝ) →ₗ[ℝ] (P ⊕ P → ℝ) where
  toFun c := fun s => match s with
    | Sum.inl x => ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0
    | Sum.inr y => ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0
  map_add' c d := by
    funext s; cases s <;>
    · simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> ring)
  map_smul' r c := by
    funext s; cases s <;>
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> ring)


noncomputable def margL :
    EuclideanSpace ℝ (OrderPairs P) →ₗ[ℝ] EuclideanSpace ℝ (P ⊕ P) :=
  (WithLp.linearEquiv 2 ℝ (P ⊕ P → ℝ)).symm.toLinearMap ∘ₗ pmargL ∘ₗ
    (WithLp.linearEquiv 2 ℝ (OrderPairs P → ℝ)).toLinearMap


noncomputable def margCLM :
    EuclideanSpace ℝ (OrderPairs P) →L[ℝ] EuclideanSpace ℝ (P ⊕ P) :=
  LinearMap.toContinuousLinearMap margL

end Transport
end StatMech
