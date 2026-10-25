/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part3


namespace StatMech.FrontierA

open SimpleGraph

theorem triangularTorusSplitEmbedHom_mapDart_of_matching
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
    (triangularTorusSplitEmbedHom L).mapDart d =
      triangularTorusDartEquiv (3 * L)
        (triangularTorusSplitEmbedVertex L d.fst,
          triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) d.fst)) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change triangularTorusSplitEmbedVertex L d.snd = _
    rw [triangularTorusSplitEmbedVertex_matching L hmatching]
    have hsnd := triangularTorusGraphDart_snd_eq_fst_add_intStep
      (3 * L) (triangularTorusDartEquiv (3 * L)
        (triangularTorusSplitEmbedVertex L d.fst,
          triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) d.fst)))
    change (triangularTorusDartEquiv (3 * L)
        (triangularTorusSplitEmbedVertex L d.fst,
          triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) d.fst))).snd = _ at hsnd
    rw [triangularTorusGraphDartDirection_dartEquiv] at hsnd
    exact hsnd.symm


end StatMech.FrontierA
