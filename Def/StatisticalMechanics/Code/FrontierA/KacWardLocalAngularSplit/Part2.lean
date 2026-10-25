/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwLocalAngularSplitBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ) :=
  kwOrderedSplitTransitionInBlocks G (data.order)
    (kwGraphTransition
      (kwOrderedDartPortSplitGraph G (data.order))
      (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data))

end StatMech.FrontierA
