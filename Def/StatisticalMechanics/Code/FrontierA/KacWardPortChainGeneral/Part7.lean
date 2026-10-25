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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part7
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


def KWOrderedExternalSplitDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :=
  {delta : (kwOrderedDartPortSplitGraph G order).Dart //
    kwDartOfPort G delta.snd = (kwDartOfPort G delta.fst).symm}


noncomputable def kwOrderedExternalSplitDartOfDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : G.Dart) : KWOrderedExternalSplitDart G order := by
  let p := kwPortOfDart G d
  let q := kwPortOfDart G d.symm
  have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q := by
    rw [kwOrderedDartPortSplitGraph_adj]
    left
    simp [p, q]
  refine ⟨⟨(p, q), hpq⟩, ?_⟩
  simp [p, q]

end StatMech.FrontierA
