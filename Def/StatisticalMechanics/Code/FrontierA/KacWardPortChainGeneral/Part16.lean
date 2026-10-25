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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part15
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedSplitWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) : Sym2 (KWDartPort G) → ℂ :=
  Sym2.lift ⟨fun p q ↦
    if kwDartOfPort G q = (kwDartOfPort G p).symm
      then weight (kwDartOfPort G p).edge else 1, by
    intro p q
    change (if kwDartOfPort G q = (kwDartOfPort G p).symm
        then weight (kwDartOfPort G p).edge else 1) =
      if kwDartOfPort G p = (kwDartOfPort G q).symm
        then weight (kwDartOfPort G q).edge else 1
    by_cases hpq : kwDartOfPort G q = (kwDartOfPort G p).symm
    · have hqp : kwDartOfPort G p = (kwDartOfPort G q).symm := by
        rw [hpq]
        exact (kwDartOfPort G p).symm_symm.symm
      rw [if_pos hpq, if_pos hqp]
      rw [hpq]
      exact (congrArg weight (kwDartOfPort G p).edge_symm).symm
    · have hqp : ¬kwDartOfPort G p = (kwDartOfPort G q).symm := by
        intro h
        apply hpq
        rw [h]
        exact (kwDartOfPort G q).symm_symm.symm
      rw [if_neg hpq, if_neg hqp]⟩

end StatMech.FrontierA
