/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Def.StatisticalMechanics.Code.Foundations.StrassenFull.Part2
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


theorem margCLM_inl (c : EuclideanSpace ℝ (OrderPairs P)) (x : P) :
    margCLM c (Sum.inl x) = ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0 := rfl

theorem margCLM_inr (c : EuclideanSpace ℝ (OrderPairs P)) (y : P) :
    margCLM c (Sum.inr y) = ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0 := rfl


theorem marg_inner (c : EuclideanSpace ℝ (OrderPairs P)) (w : EuclideanSpace ℝ (P ⊕ P)) :
    (inner ℝ (margCLM c) w : ℝ)
      = ∑ q : OrderPairs P, c q * (w (Sum.inl (q : P × P).1) + w (Sum.inr (q : P × P).2)) := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [RCLike.inner_apply, conj_trivial]
  have e1 : ∀ x : P, (margCLM c) (Sum.inl x)
      = ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0 := fun x => margCLM_inl c x
  have e2 : ∀ y : P, (margCLM c) (Sum.inr y)
      = ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0 := fun y => margCLM_inr c y
  simp only [e1, e2]
  have hL : (∑ x, w (Sum.inl x) * ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0)
      = ∑ q : OrderPairs P, c q * w (Sum.inl (q : P × P).1) := by
    have hstep : ∀ x : P, w (Sum.inl x) * ∑ q : OrderPairs P, (if (q : P × P).1 = x then c q else 0)
        = ∑ q : OrderPairs P, (if (q : P × P).1 = x then c q * w (Sum.inl x) else 0) := by
      intro x; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> ring)
    rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_ite_eq Finset.univ (q : P × P).1 (fun x => c q * w (Sum.inl x))]
    simp
  have hR : (∑ y, w (Sum.inr y) * ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0)
      = ∑ q : OrderPairs P, c q * w (Sum.inr (q : P × P).2) := by
    have hstep : ∀ y : P, w (Sum.inr y) * ∑ q : OrderPairs P, (if (q : P × P).2 = y then c q else 0)
        = ∑ q : OrderPairs P, (if (q : P × P).2 = y then c q * w (Sum.inr y) else 0) := by
      intro y; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by split_ifs <;> ring)
    rw [Finset.sum_congr rfl (fun y _ => hstep y), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_ite_eq Finset.univ (q : P × P).2 (fun y => c q * w (Sum.inr y))]
    simp
  rw [hL, hR, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun q _ => by ring)

end Transport
end StatMech
