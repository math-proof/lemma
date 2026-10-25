/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned.Part4
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


theorem lpTwoGhost_bondSum_pinned
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (h : W -> Real) (side : W -> Bool) (tau : ConfigSpace W) :
    (∑ e ∈ lpTwoGhostEdges E side,
        lpTwoGhostCoupling J h side e *
          bond (lpTwoGhostPinnedConfig tau) e) =
      (∑ e ∈ E, J e * bond tau e) +
        ∑ x : W, lpTwoGhostMixedField h side x * spin tau x := by
  rw [lpTwoGhostEdges,
    Finset.sum_union (lpTwoGhostBaseEdges_disjoint_star E side)]
  congr 1
  · rw [lpTwoGhostBaseEdges, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e _
      induction e with
      | h x y =>
          rw [Sym2.map_mk, lpTwoGhostCoupling_base, bond_mk, bond_mk]
          rfl
    · intro a _ b _ hab
      exact Sym2.map.injective Sum.inl_injective hab
  · rw [lpTwoGhostStarEdges,
      Finset.sum_image (lpTwoGhostStarEdge_injective side).injOn]
    apply Finset.sum_congr rfl
    intro x _
    rw [lpTwoGhostCoupling_star, bond_mk]
    by_cases hs : side x
    · simp [lpTwoGhostMixedField, hs]
    · simp [lpTwoGhostMixedField, hs]


theorem lpTwoGhost_weight_pinned_eq
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (h : W -> Real) (side : W -> Bool) (tau : ConfigSpace W) :
    wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side)
        (fun _ => 0) (lpTwoGhostPinnedConfig tau) =
      wJ E J (lpTwoGhostMixedField h side) tau := by
  unfold wJ
  rw [lpTwoGhost_bondSum_pinned]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]


theorem lpTwoGhost_pinnedPartition_eq
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (h : W -> Real) (side : W -> Bool) :
    (∑ tau : ConfigSpace W,
      wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side)
        (fun _ => 0) (lpTwoGhostPinnedConfig tau)) =
      ZJ E J (lpTwoGhostMixedField h side) := by
  unfold ZJ
  apply Finset.sum_congr rfl
  intro tau _
  exact lpTwoGhost_weight_pinned_eq E J h side tau


theorem lpTwoGhost_pinnedExp_eq
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (h : W -> Real) (side : W -> Bool)
    (F : ConfigSpace W -> Real) :
    (∑ tau : ConfigSpace W,
        F tau *
          wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side)
            (fun _ => 0) (lpTwoGhostPinnedConfig tau)) /
      (∑ tau : ConfigSpace W,
        wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side)
          (fun _ => 0) (lpTwoGhostPinnedConfig tau)) =
      expJ E J (lpTwoGhostMixedField h side) F := by
  rw [lpTwoGhost_pinnedPartition_eq]
  unfold expJ
  congr 1
  apply Finset.sum_congr rfl
  intro tau _
  rw [lpTwoGhost_weight_pinned_eq]


end
end StatMech.Ising
