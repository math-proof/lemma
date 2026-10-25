/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
open SimpleGraph


namespace StatMech.FrontierD

theorem sum_bool_toNat_eq_sixVertexUpCount
    {N : Nat} (x : SixVertexRow N) :
    (∑ i, (x i).toNat) = sixVertexUpCount x := by
  classical
  unfold sixVertexUpCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x i <;> simp [h]


theorem fkOrientedLoopVerticalFlux_eq_charge
    (T : EvenTorus) (omega : SixVertexArrows T) :
    fkOrientedLoopVerticalFlux T omega =
      2 * (sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) : Int) -
        (T.width : Int) := by
  classical
  let x := svTorusVerticalRows T omega (svFinLast T.height_pos)
  have hc : (∑ i, (x i).toNat) = sixVertexUpCount x :=
    sum_bool_toNat_eq_sixVertexUpCount x
  have hcInt : (∑ i, ((x i).toNat : Int)) =
      (sixVertexUpCount x : Int) := by
    exact_mod_cast hc
  unfold fkOrientedLoopVerticalFlux
  change (∑ i, if x i then (1 : Int) else -1) = _
  calc
    (∑ i, if x i then (1 : Int) else -1) =
        ∑ i, (2 * ((x i).toNat : Int) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      cases x i <;> simp
    _ = 2 * (∑ i, ((x i).toNat : Int)) - (T.width : Int) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      simp
    _ = 2 * (sixVertexUpCount x : Int) - (T.width : Int) := by
      rw [hcInt]


theorem fkOrientedLoopVerticalFlux_eq_neg_two_mul_of_fixedCharge
    (T : EvenTorus) (omega : SixVertexArrows T)
    (r : Nat) (hr : r <= T.width / 2)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) =
        T.width / 2 - r) :
    fkOrientedLoopVerticalFlux T omega = -(2 * (r : Int)) := by
  rw [fkOrientedLoopVerticalFlux_eq_charge, hsector]
  obtain ⟨k, hk⟩ := T.width_even
  have hw : T.width / 2 = k := by omega
  have hrk : r <= k := by rwa [<- hw]
  rw [hw, hk]
  push_cast [Nat.cast_sub hrk]
  ring

end StatMech.FrontierD
