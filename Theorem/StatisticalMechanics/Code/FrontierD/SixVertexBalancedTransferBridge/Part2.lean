/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part2
open Finset Matrix


namespace StatMech.FrontierD

theorem svHorizontalIce_step {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h)
    (i : Fin N) :
    (h i).toNat + (y i).toNat =
      (h (SixVertexArrows.cyclicPred hN i)).toNat + (x i).toNat := by
  have hi := hice i
  unfold svHorizontalIncomingCount at hi
  cases hx : x i <;> cases hy : y i <;>
    cases hp : h (SixVertexArrows.cyclicPred hN i) <;>
    cases hh : h i <;> simp [hx, hy, hp, hh] at hi ⊢

theorem svHorizontalIce_prefix {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h)
    (k : Fin N) :
    (h k).toNat + svRowPrefixCount y k =
      (h (svFinLast hN)).toNat + svRowPrefixCount x k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  induction k using Fin.induction with
  | zero =>
      rw [svRowPrefixCount_zero, svRowPrefixCount_zero]
      have hs := svHorizontalIce_step (Nat.succ_pos m) hice (0 : Fin (m + 1))
      simpa [SixVertexArrows.cyclicPred] using hs
  | succ i ih =>
      rw [svRowPrefixCount_succ, svRowPrefixCount_succ]
      have hs := svHorizontalIce_step (Nat.succ_pos m) hice i.succ
      have hpred : SixVertexArrows.cyclicPred (Nat.succ_pos m) i.succ =
          i.castSucc := by
        ext
        simp only [SixVertexArrows.cyclicPred, Fin.val_succ, Fin.val_castSucc]
        rw [show i.val + 1 + (m + 1) - 1 = (m + 1) + i.val by omega,
          Nat.add_mod_left,
          Nat.mod_eq_of_lt (i.isLt.trans (Nat.lt_succ_self m))]
      rw [hpred] at hs
      omega

end StatMech.FrontierD
