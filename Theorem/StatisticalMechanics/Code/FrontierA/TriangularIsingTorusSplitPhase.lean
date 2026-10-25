/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitPhase


namespace StatMech.FrontierA

open SimpleGraph


theorem triangularTorusSplitEmbedHom_mapDart_direction
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) :
    triangularTorusGraphDartDirection (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d) =
      triangularTorusSplitDartDirection L d := by
  classical
  by_cases hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm
  · calc
      triangularTorusGraphDartDirection (3 * L)
          ((triangularTorusSplitEmbedHom L).mapDart d) =
          triangularTorusGraphDartDirection (3 * L)
            (triangularTorusDartEquiv (3 * L)
              (triangularTorusSplitEmbedVertex L d.fst,
                triangularTorusGraphDartDirection L
                  (kwDartOfPort (triangularTorusGraph L) d.fst))) := by
            rw [triangularTorusSplitEmbedHom_mapDart_of_matching L d hmatching]
      _ = triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) d.fst) :=
        triangularTorusGraphDartDirection_dartEquiv _ _
      _ = triangularTorusSplitDartDirection L d := by
        simp [triangularTorusSplitDartDirection, hmatching]
  · have hint := (kwOrderedDartPortSplitGraph_adj
        (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
        d.fst d.snd).mp d.adj |>.resolve_left hmatching
    generalize ha : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) d.fst) = a
    generalize hb : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) d.snd) = b
    let c := triangularTorusSplitInternalDirection a b
    have hembed : triangularTorusSplitEmbedVertex L d.snd =
        triangularTorusSplitEmbedVertex L d.fst +
          (((triangularIntStep c).1 : ZMod (3 * L)),
            ((triangularIntStep c).2 : ZMod (3 * L))) := by
      have howner : d.fst.1 = d.snd.1 := hint.1
      have hrank : (triangularTorusDirectionRank a).val + 1 =
            (triangularTorusDirectionRank b).val ∨
          (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank a).val := by
        simpa [triangularTorusLocalPortOrder_rank, ha, hb] using hint.2
      rw [triangularTorusSplitEmbedVertex_eq_cast,
        triangularTorusSplitEmbedVertex_eq_cast, ← howner]
      rw [ha, hb]
      apply Prod.ext
      · change (3 : ZMod (3 * L)) * ZMod.cast d.fst.1.1 +
            ((triangularTorusSplitOffset b).1 : ZMod (3 * L)) =
          ((3 : ZMod (3 * L)) * ZMod.cast d.fst.1.1 +
            ((triangularTorusSplitOffset a).1 : ZMod (3 * L))) +
              ((triangularIntStep c).1 : ZMod (3 * L))
        rcases hrank with hrank | hrank <;>
          fin_cases a <;> fin_cases b <;>
          simp [triangularTorusDirectionRank,
            triangularTorusSplitInternalDirection,
            triangularTorusSplitIncreasingDirection,
            triangularTorusSplitOffset, triangularTorusDirectionReverse,
            triangularIntStep, c] at hrank ⊢ <;> ring
      · change (3 : ZMod (3 * L)) * ZMod.cast d.fst.1.2 +
            ((triangularTorusSplitOffset b).2 : ZMod (3 * L)) =
          ((3 : ZMod (3 * L)) * ZMod.cast d.fst.1.2 +
            ((triangularTorusSplitOffset a).2 : ZMod (3 * L))) +
              ((triangularIntStep c).2 : ZMod (3 * L))
        rcases hrank with hrank | hrank <;>
          fin_cases a <;> fin_cases b <;>
          simp [triangularTorusDirectionRank,
            triangularTorusSplitInternalDirection,
            triangularTorusSplitIncreasingDirection,
            triangularTorusSplitOffset, triangularTorusDirectionReverse,
            triangularIntStep, c] at hrank ⊢ <;> ring
    have hdart : (triangularTorusSplitEmbedHom L).mapDart d =
        triangularTorusDartEquiv (3 * L)
          (triangularTorusSplitEmbedVertex L d.fst, c) := by
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · rfl
      · change triangularTorusSplitEmbedVertex L d.snd = _
        rw [hembed]
        have hsnd := triangularTorusGraphDart_snd_eq_fst_add_intStep
          (3 * L) (triangularTorusDartEquiv (3 * L)
            (triangularTorusSplitEmbedVertex L d.fst, c))
        rw [triangularTorusGraphDartDirection_dartEquiv] at hsnd
        exact hsnd.symm
    rw [hdart, triangularTorusGraphDartDirection_dartEquiv]
    simp [triangularTorusSplitDartDirection, hmatching, c, ha, hb]


end StatMech.FrontierA
