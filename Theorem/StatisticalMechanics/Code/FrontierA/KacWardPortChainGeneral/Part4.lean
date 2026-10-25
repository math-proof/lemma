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
import Instance.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwDartPortSplitGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : KWDartPort G) :
    (kwDartPortSplitGraph G).Adj p q ↔
      kwDartOfPort G q = (kwDartOfPort G p).symm ∨
        (p.1 = q.1 ∧
          (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) :=
  Iff.rfl


theorem kwDartPortSplitGraph_degree_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : KWDartPort G) :
    (kwDartPortSplitGraph G).degree p ≤ 3 := by
  classical
  let code : (kwDartPortSplitGraph G).neighborSet p → Fin 3 := fun q ↦
    if kwDartOfPort G q.1 = (kwDartOfPort G p).symm then 0
    else if q.1.2.val + 1 = p.2.val then 1
    else 2
  have hcode : Function.Injective code := by
    intro q r hqr
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    simp only [code] at hqr
    rw [SimpleGraph.mem_neighborSet, kwDartPortSplitGraph_adj] at hq hr
    by_cases hqext : kwDartOfPort G q = (kwDartOfPort G p).symm
    · have hrext : kwDartOfPort G r = (kwDartOfPort G p).symm := by
        by_contra hne
        simp only [hqext, ↓reduceIte, hne] at hqr
        split at hqr <;> omega
      apply Subtype.ext
      exact kwDartOfPort_injective G (hqext.trans hrext.symm)
    · by_cases hrext : kwDartOfPort G r = (kwDartOfPort G p).symm
      · simp only [hqext, hrext, ↓reduceIte] at hqr
        split at hqr <;> omega
      · have hqdata := hq.resolve_left hqext
        have hrdata := hr.resolve_left hrext
        by_cases hqpred : q.2.val + 1 = p.2.val
        · have hrpred : r.2.val + 1 = p.2.val := by
            by_contra hne
            simp [hqext, hrext, hqpred, hne] at hqr
          apply Subtype.ext
          apply kwDartPort_eq_of_fst_of_val G
              (hqdata.1.symm.trans hrdata.1)
          omega
        · have hrpred : ¬(r.2.val + 1 = p.2.val) := by
            intro hp
            simp [hqext, hrext, hqpred, hp] at hqr
          have hqsucc : p.2.val + 1 = q.2.val :=
            hqdata.2.resolve_right hqpred
          have hrsucc : p.2.val + 1 = r.2.val :=
            hrdata.2.resolve_right hrpred
          apply Subtype.ext
          apply kwDartPort_eq_of_fst_of_val G
              (hqdata.1.symm.trans hrdata.1)
          omega
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective code hcode


end StatMech.FrontierA
