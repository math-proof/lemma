/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Def.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

open StatMech.Ising (bond)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem shb_weight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (n : Current V) : 0 ≤ weight G β J n := by
  unfold weight
  apply Finset.prod_nonneg
  intro e _
  exact div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (by positivity)


theorem shb_summable_weight (β : ℝ) (J : Sym2 V → ℝ) :
    Summable (fun m : ↥G.edgeFinset → ℕ => weight G β J (ofEdgeFun G m)) := by
  have h := summable_weight_bond G β J (fun _ => true)
  refine h.congr (fun m => ?_)
  have hone : ∀ e : ↥G.edgeFinset, (bond (fun _ => true) e.1) = 1 := by
    intro e; refine Sym2.ind (fun a b => ?_) e.1; simp [bond]
  simp only [hone, one_pow, Finset.prod_const_one, mul_one]


theorem shb_summable_indicator (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (P : (↥G.edgeFinset → ℕ) → Prop) [DecidablePred P] :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      if P m then weight G β J (ofEdgeFun G m) else 0) := by
  refine (shb_summable_weight G β J).of_nonneg_of_le ?_ ?_
  · intro m; split <;> [exact shb_weight_nonneg G β J hβ hJ _; rfl]
  · intro m; split <;> [exact le_refl _; exact shb_weight_nonneg G β J hβ hJ _]


end Sharpness
end StatMech
