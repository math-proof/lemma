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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part16
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwOrderedSplitWeight_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (order : KWPortOrder G) (d : G.Dart) :
    kwOrderedSplitWeight G weight
        (kwOrderedExternalSplitDartOfDart G order d).1.edge =
      weight d.edge := by
  unfold kwOrderedSplitWeight SimpleGraph.Dart.edge
  rw [Sym2.lift_mk]
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd,
    kwDartOfPort_portOfDart, if_pos]

theorem kwOrderedSplitWeight_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) :
    kwOrderedSplitWeight G weight d.1.edge = 1 := by
  unfold kwOrderedSplitWeight SimpleGraph.Dart.edge
  rw [Sym2.lift_mk]
  change (if kwDartOfPort G d.1.snd = (kwDartOfPort G d.1.fst).symm
    then weight (kwDartOfPort G d.1.fst).edge else 1) = 1
  rw [if_neg d.2]


end StatMech.FrontierA
