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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part31
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwPortSplitAdjBit_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G)
    {p q : KWDartPort G} (hpq : (kwDartPortSplitGraph G).Adj p q) :
    kwPortSplitAdjBit G b y p q = kwPortSplitAdjBit G b y q p := by
  rw [kwDartPortSplitGraph_adj] at hpq
  by_cases hext : kwDartOfPort G q = (kwDartOfPort G p).symm
  · have hrev : kwDartOfPort G p = (kwDartOfPort G q).symm := by
      rw [hext]
      exact (kwDartOfPort G p).symm_symm.symm
    rw [kwPortSplitAdjBit, if_pos hext, kwPortSplitAdjBit, if_pos hrev]
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
    by_cases hpred : j.val + 1 = i.val
    · have hnotSucc : ¬(i.val + 1 = j.val) := by omega
      simp only [kwPortSplitAdjBit, hext, hrev, hpred, hnotSucc,
        ↓reduceIte]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.succ]
      omega
    · have hsucc : i.val + 1 = j.val := hidx.resolve_right hpred
      simp only [kwPortSplitAdjBit, hext, hrev, hpred, hsucc,
        ↓reduceIte]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.succ]
      exact hsucc


end StatMech.FrontierA
