/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part4


namespace StatMech.FrontierD

theorem finitePeriodicSucc_ne_self {N : Nat} (hN : 1 < N) (i : Fin N) :
    finitePeriodicSucc (lt_trans Nat.zero_lt_one hN) i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  simp only [finitePeriodicSucc, Fin.val_mk] at hval
  by_cases hi : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt hi] at hval
    omega
  · have hieq : i.val + 1 = N := by omega
    rw [hieq, Nat.mod_self] at hval
    omega

theorem cyclicPred_ne_self {N : Nat} (hN : 1 < N) (i : Fin N) :
    SixVertexArrows.cyclicPred (lt_trans Nat.zero_lt_one hN) i ≠ i := by
  intro h
  have hsucc := congrArg
    (finitePeriodicSucc (lt_trans Nat.zero_lt_one hN)) h
  rw [finitePeriodicSucc_cyclicPred] at hsucc
  exact finitePeriodicSucc_ne_self hN i hsucc.symm

theorem fkRectTorusIndexedEdge_ne_diag (R : FKRectTorus)
    (a : R.EdgeIndex) (x : R.Vertex) :
    fkRectTorusIndexedEdge R a ≠ s(x, x) := by
  intro ha
  rcases a with ⟨dir, a⟩
  cases dir
  · simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, ↓reduceIte] at ha
    split at ha <;> rcases Sym2.eq_iff.mp ha with heq | heq
    all_goals
      have hy := congrArg Prod.snd heq.1
      have hpred := congrArg Prod.snd heq.2
      exact cyclicPred_ne_self (lt_trans Nat.one_lt_two R.height_gt_two) a.2
        (hpred.trans hy.symm)
  · simp only [fkRectTorusIndexedEdge, ↓reduceIte] at ha
    rcases Sym2.eq_iff.mp ha with heq | heq
    · have hbase := congrArg Prod.snd heq.1
      have hpred := congrArg Prod.snd heq.2
      exact cyclicPred_ne_self (lt_trans Nat.one_lt_two R.height_gt_two) a.2
        (hpred.trans hbase.symm)
    · have hbase := congrArg Prod.snd heq.1
      have hpred := congrArg Prod.snd heq.2
      exact cyclicPred_ne_self (lt_trans Nat.one_lt_two R.height_gt_two) a.2
        (hpred.trans hbase.symm)


end StatMech.FrontierD
