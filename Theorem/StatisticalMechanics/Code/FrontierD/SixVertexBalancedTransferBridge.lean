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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge
open Finset Matrix


namespace StatMech.FrontierD

theorem svRowPrefixCount_zero {N : Nat} (x : SixVertexRow (N + 1)) :
    svRowPrefixCount x 0 = (x 0).toNat := by
  unfold svRowPrefixCount
  have hset : Finset.Iic (0 : Fin (N + 1)) = {0} := by
    ext i
    simp
  rw [hset]
  simp

theorem svRowPrefixCount_succ {N : Nat} (x : SixVertexRow (N + 1))
    (i : Fin N) :
    svRowPrefixCount x i.succ =
      svRowPrefixCount x i.castSucc + (x i.succ).toNat := by
  unfold svRowPrefixCount
  have hset : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val,
      Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [hset, Finset.sum_insert]
  · omega
  · simp

theorem svRowPrefixCount_last {N : Nat} (x : SixVertexRow (N + 1)) :
    svRowPrefixCount x (Fin.last N) = sixVertexUpCount x := by
  unfold svRowPrefixCount sixVertexUpCount
  have hset : Finset.Iic (Fin.last N) = Finset.univ := by
    exact Finset.eq_univ_of_forall fun i => Finset.mem_Iic.mpr (Fin.le_last i)
  rw [hset, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases x i <;> simp

end StatMech.FrontierD
