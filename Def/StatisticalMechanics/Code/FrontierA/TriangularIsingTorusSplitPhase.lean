/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive.Part2


namespace StatMech.FrontierA

open SimpleGraph


def triangularTorusSplitIncreasingDirection : Fin 6 -> Fin 6 :=
  ![0, 3, 5, 4, 1, 0]


def triangularTorusSplitInternalDirection (a b : Fin 6) : Fin 6 :=
  if (triangularTorusDirectionRank a).val <
      (triangularTorusDirectionRank b).val then
    triangularTorusSplitIncreasingDirection a
  else
    triangularTorusDirectionReverse
      (triangularTorusSplitIncreasingDirection b)


noncomputable def triangularTorusSplitDartDirection
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) : Fin 6 :=
  if kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm then
    triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) d.fst)
  else
    triangularTorusSplitInternalDirection
      (triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.fst))
      (triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.snd))

end StatMech.FrontierA
