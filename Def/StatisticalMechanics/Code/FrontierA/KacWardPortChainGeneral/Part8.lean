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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part8
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedExternalSplitDartEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    G.Dart ≃ KWOrderedExternalSplitDart G order where
  toFun := kwOrderedExternalSplitDartOfDart G order
  invFun delta := kwDartOfPort G delta.1.fst
  left_inv d := by simp
  right_inv delta := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · simp
    · have hmatch := delta.2
      apply kwDartOfPort_injective G
      simpa using hmatch.symm


def KWOrderedInternalSplitDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :=
  {delta : (kwOrderedDartPortSplitGraph G order).Dart //
    ¬kwDartOfPort G delta.snd = (kwDartOfPort G delta.fst).symm}

end StatMech.FrontierA
