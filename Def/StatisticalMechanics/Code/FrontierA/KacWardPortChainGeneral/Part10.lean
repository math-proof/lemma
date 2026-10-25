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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part9
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedSplitTransitionInBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (M : Matrix (kwOrderedDartPortSplitGraph G order).Dart
      (kwOrderedDartPortSplitGraph G order).Dart ℂ) :
    Matrix (G.Dart ⊕ KWOrderedInternalSplitDart G order)
      (G.Dart ⊕ KWOrderedInternalSplitDart G order) ℂ :=
  Matrix.reindex (kwOrderedSplitDartBlockEquiv G order).symm
    (kwOrderedSplitDartBlockEquiv G order).symm M

end StatMech.FrontierA
