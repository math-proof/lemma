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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part14
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedSplitInternalBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (M : Matrix (kwOrderedDartPortSplitGraph G order).Dart
      (kwOrderedDartPortSplitGraph G order).Dart ℂ) :
    Matrix (KWOrderedInternalSplitDart G order)
      (KWOrderedInternalSplitDart G order) ℂ :=
  (kwOrderedSplitTransitionInBlocks G order M).toBlocks₂₂


noncomputable def kwOrderedInternalPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ)
    (d e : (kwOrderedPortInternalGraph G order).Dart) : ℂ :=
  phase ((kwOrderedInternalSplitDartEquiv G order).symm d).1
    ((kwOrderedInternalSplitDartEquiv G order).symm e).1

end StatMech.FrontierA
