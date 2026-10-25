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
import Instance.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part9
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwDartPortSplitEvenEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    KWOriginalEvenBits G ≃ KWSplitEvenBits G where
  toFun b := ⟨⟨b.1, kwCanonicalPortChainField G b.1⟩,
    kwCanonicalPortChainField_even G b.1 b.2⟩
  invFun p := ⟨p.1.1,
    kwOriginalPortEven_of_globalPortChainEven G p.1.1 p.1.2 p.2⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (kwPortChainField_eq_canonical G p.1.1 p.1.2 p.2).symm


end StatMech.FrontierA
