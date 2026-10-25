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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwDartPortSplitGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph (KWDartPort G) where
  Adj p q :=
    kwDartOfPort G q = (kwDartOfPort G p).symm ∨
      (p.1 = q.1 ∧
        (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val))
  symm := by
    constructor
    intro p q h
    rcases h with h | ⟨hfst, hidx⟩
    · left
      rw [h]
      exact (kwDartOfPort G p).symm_symm.symm
    · right
      exact ⟨hfst.symm, hidx.symm⟩
  loopless := ⟨by
    intro p h
    rcases h with h | ⟨-, hidx⟩
    · exact (kwDartOfPort G p).symm_ne h.symm
    · omega⟩

end StatMech.FrontierA
