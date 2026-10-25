/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part29
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedPortSplitAdjBit_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) {p q : KWDartPort G}
    (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q) :
    kwOrderedPortSplitAdjBit G order b y p q =
      kwOrderedPortSplitAdjBit G order b y q p := by
  rw [kwOrderedDartPortSplitGraph_adj] at hpq
  by_cases hext : kwDartOfPort G q = (kwDartOfPort G p).symm
  · have hrev : kwDartOfPort G p = (kwDartOfPort G q).symm := by
      rw [hext]
      exact (kwDartOfPort G p).symm_symm.symm
    rw [kwOrderedPortSplitAdjBit, if_pos hext,
      kwOrderedPortSplitAdjBit, if_pos hrev]
    unfold kwExternalPortBits
    rw [hext, b.2]
  · have hrev : ¬kwDartOfPort G p = (kwDartOfPort G q).symm := by
      intro h
      apply hext
      rw [h]
      exact (kwDartOfPort G q).symm_symm.symm
    rcases hpq.resolve_left hext with ⟨hfst, hidx⟩
    rcases p with ⟨v, i⟩
    rcases q with ⟨w, j⟩
    dsimp only at hfst hidx ⊢
    subst w
    by_cases hpred : (order v j).val + 1 = (order v i).val
    · have hnotSucc : ¬((order v i).val + 1 = (order v j).val) := by
        omega
      have hpred' : kwOrderedPortRank order ⟨v, j⟩ + 1 =
          kwOrderedPortRank order ⟨v, i⟩ := hpred
      have hnotSucc' : ¬(kwOrderedPortRank order ⟨v, i⟩ + 1 =
          kwOrderedPortRank order ⟨v, j⟩) := hnotSucc
      rw [kwOrderedPortSplitAdjBit, if_neg hext, if_pos hpred',
        kwOrderedPortSplitAdjBit, if_neg hrev, if_neg hnotSucc']
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.succ]
      exact hpred.symm
    · have hsucc : (order v i).val + 1 = (order v j).val :=
        hidx.resolve_right hpred
      have hpred' : ¬(kwOrderedPortRank order ⟨v, j⟩ + 1 =
          kwOrderedPortRank order ⟨v, i⟩) := hpred
      have hsucc' : kwOrderedPortRank order ⟨v, i⟩ + 1 =
          kwOrderedPortRank order ⟨v, j⟩ := hsucc
      rw [kwOrderedPortSplitAdjBit, if_neg hext, if_neg hpred',
        kwOrderedPortSplitAdjBit, if_neg hrev, if_pos hsucc']
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.succ]
      exact hsucc


end StatMech.FrontierA
