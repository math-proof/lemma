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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part4
open Finset Matrix


namespace StatMech.FrontierD

theorem svCyclicPred_zero {N : Nat} (hN : 0 < N) :
    SixVertexArrows.cyclicPred hN (⟨0, hN⟩ : Fin N) = svFinLast hN := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  ext
  simp [SixVertexArrows.cyclicPred, svFinLast]

theorem svCyclicPred_succ {N : Nat} (i : Fin N) :
    SixVertexArrows.cyclicPred (Nat.succ_pos N) i.succ = i.castSucc := by
  ext
  simp only [SixVertexArrows.cyclicPred, Fin.val_succ, Fin.val_castSucc]
  rw [show i.val + 1 + (N + 1) - 1 = (N + 1) + i.val by omega,
    Nat.add_mod_left,
    Nat.mod_eq_of_lt (i.isLt.trans (Nat.lt_succ_self N))]

theorem svHorizontalIce_iff_prefixRelation {N : Nat} (hN : 0 < N)
    (x y h : SixVertexRow N) :
    svHorizontalIce hN x y h ↔ svHorizontalPrefixRelation hN x y h := by
  constructor
  · intro hice
    exact svHorizontalIce_prefix hN hice
  · intro hrel i
    have hstep : (h i).toNat + (y i).toNat =
        (h (SixVertexArrows.cyclicPred hN i)).toNat + (x i).toNat := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      induction i using Fin.induction with
      | zero =>
          have h0 := hrel (0 : Fin (m + 1))
          rw [svRowPrefixCount_zero, svRowPrefixCount_zero] at h0
          have hpred : SixVertexArrows.cyclicPred hN (0 : Fin (m + 1)) =
              svFinLast hN := by
            ext
            simp [SixVertexArrows.cyclicPred, svFinLast]
          rw [hpred]
          exact h0
      | succ i ih =>
          have hsucc := hrel i.succ
          have hprev := hrel i.castSucc
          rw [svRowPrefixCount_succ, svRowPrefixCount_succ] at hsucc
          rw [svCyclicPred_succ]
          omega
    unfold svHorizontalIncomingCount
    cases hx : x i <;> cases hy : y i <;>
      cases hp : h (SixVertexArrows.cyclicPred hN i) <;>
      cases hh : h i <;> simp [hx, hy, hp, hh] at hstep ⊢

end StatMech.FrontierD
